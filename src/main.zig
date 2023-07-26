const std = @import("std");
const testing = std.testing;
const mem = std.mem;

var nodes: usize = 0;

pub const PlayerType = enum(u8) {
    black_piece,
    white_piece,
};

pub const SquareType = enum(u8) {
    black_square,
    white_square,
    void,
};

pub const Position = struct {
    x: usize,
    y: usize,
};

pub const Movement = struct {
    player: PlayerType,
    position: Position,
};

pub const Difficulty = enum {
    easy,
    medium,
    hard,
};

pub const EndState = enum {
    winner,
    loser,
    tie,
};

pub const Player = struct {
    is_human: bool,
};

pub const Game = struct {
    allocator: mem.Allocator,
    board: Board,
    player1: Player,
    player2: Player,
    difficulty: Difficulty,
    history_forwards: std.ArrayList(Movement),
    history_backwards: std.ArrayList(Movement),
    last_move_player: PlayerType = PlayerType.white_piece,
    size: usize,
    initial_board: ?Board = null,
    heuristic_values: [][]isize,

    pub fn newGameAI(allocator: mem.Allocator, size: usize, difficulty: Difficulty) !Game {
        if (size % 2 != 0) {
            return error.BadValue;
        }
        var board = try Game.getInitialBoard(allocator, size);
        var heuristic_values = try Game.getHeuristicValues(allocator, size);
        var game = Game{
            .allocator = allocator,
            .board = board,
            .player1 = Player{ .is_human = true },
            .player2 = Player{ .is_human = false },
            .difficulty = difficulty,
            .history_forwards = std.ArrayList(Movement).init(allocator),
            .history_backwards = std.ArrayList(Movement).init(allocator),
            .size = size,
            .heuristic_values = heuristic_values,
        };
        return game;
    }

    fn getInitialBoard(allocator: mem.Allocator, size: usize) !Board {
        var board = try allocator.alloc([]SquareType, size);

        // Create rows
        for (0..size) |index| {
            var row = try allocator.alloc(SquareType, size);
            @memset(row, SquareType.void);
            board[index] = row;
        }

        // Set initial pieces
        board[size / 2 - 1][size / 2 - 1] = SquareType.white_square;
        board[size / 2 - 1][size / 2] = SquareType.black_square;
        board[size / 2][size / 2 - 1] = SquareType.black_square;
        board[size / 2][size / 2] = SquareType.white_square;

        return board;
    }

    fn getHeuristicValues(allocator: mem.Allocator, size: usize) ![][]isize {
        var values = try allocator.alloc([]isize, size);

        for (0..size) |index| {
            var row = try allocator.alloc(isize, size);
            values[index] = row;
        }

        for (0..size) |index| {
            values[1][index] = -20;
            values[size - 2][index] = -20;
            if (index < size - 4) {
                values[0][index + 2] = 7;
                values[size - 1][index + 2] = 7;
            }
            for (0..size) |j| {
                values[j][1] = -20;
                values[j][size - 2] = -20;
                if (j < size - 4) {
                    values[j + 2][0] = 7;
                    values[j + 2][size - 1] = 7;
                }
                if (j < size - 4 and index < size - 4) {
                    values[j + 2][index + 2] = 4;
                }
            }
        }

        for (1..3) |i| {
            var value = i % 2;
            var is_negative: isize = if (@as(isize, @intCast(value)) == 0) -1 else 1;
            values[value][value] = @divFloor(@as(isize, 100), (@as(isize, @intCast(value)) + 1) * is_negative);
            values[size - 1 - value][value] = @divFloor(@as(isize, 100), (@as(isize, @intCast(value)) + 1) * is_negative);
            values[value][size - 1 - value] = @divFloor(@as(isize, 100), (@as(isize, @intCast(value)) + 1) * is_negative);
            values[size - 1 - value][size - value - 1] = @divFloor(@as(isize, 100), (@as(isize, @intCast(value)) + 1) * is_negative);
        }

        return values;
    }

    pub fn deinitBoard(board: Board, allocator: mem.Allocator) void {
        for (board) |row| {
            allocator.free(row);
        }
        allocator.free(board);
    }

    pub fn isValidMove(self: *Game, board: Board, move: Movement) bool {
        const opponent = @intFromEnum(if (move.player == PlayerType.black_piece)
            PlayerType.white_piece
        else
            PlayerType.black_piece);
        var size = self.size;

        const Tuple = struct { comptime_int, comptime_int };

        inline for (comptime [_]Tuple{
            .{ -1, -1 }, .{ -1, 1 }, .{ 1, -1 }, .{ 1, 1 },
            .{ 0, 1 },   .{ 0, -1 }, .{ 1, 0 },  .{ -1, 0 },
        }) |values| {
            const first = values.@"0";
            const second = values.@"1";

            var col_index: isize = @as(isize, @intCast(move.position.x)) + first;
            var row_index: isize = @as(isize, @intCast(move.position.y)) + second;
            var offset: usize = 0;

            while ((col_index > 0 and col_index < size) and (row_index > 0 and row_index < size) and
                @intFromEnum(board[@intCast(row_index)][@intCast(col_index)]) == opponent)
            {
                offset += 1;
                col_index += first;
                row_index += second;
            } else if ((col_index > 0 and col_index < size) and (row_index > 0 and row_index < size) and
                @intFromEnum(board[@intCast(row_index)][@intCast(col_index)]) == @intFromEnum(move.player) and
                offset > 0)
            {
                return true;
            }
        }

        return false;
    }

    fn makeMoveAllocator(self: *Game, move: Movement, allocator: mem.Allocator) !void {
        return try self.makeMoveBoard(&self.board, move, allocator);
    }

    pub fn goBack(self: *Game) !void {
        Game.deinitBoard(self.board, self.allocator);
        if (self.initial_board) |initial_board| {
            try self.copyBoard(&self.board, initial_board, self.allocator);
        } else {
            self.board = try Game.getInitialBoard(self.allocator, self.size);
        }
        try self.history_forwards.append(self.history_backwards.pop());

        for (self.history_backwards.items) |move| {
            try self.makeMove(move);
        }
    }

    pub fn goForward(self: *Game) !void {
        var move = self.history_forwards.pop();

        try self.makeRealMove(move);
    }

    pub fn canGoBack(self: *Game) bool {
        return self.history_backwards.items.len > 0;
    }

    pub fn canGoForward(self: *Game) bool {
        return self.history_forwards.items.len > 0;
    }

    pub fn makeRealMove(self: *Game, move: Movement) !void {
        try self.history_backwards.append(move);
        return try self.makeMoveBoard(&self.board, move, self.allocator);
    }

    fn makeMove(self: *Game, move: Movement) !void {
        return try self.makeMoveBoard(&self.board, move, self.allocator);
    }

    pub fn copyBoard(self: *Game, dest: *Board, source: Board, allocator: mem.Allocator) !void {
        dest.* = try allocator.alloc([]SquareType, self.size);

        for (0..self.size) |index| {
            var row = try allocator.alloc(SquareType, self.size);
            @memcpy(row, source[index]);
            dest.*[index] = row;
        }
    }

    pub fn nextTurn(self: *Game) ?PlayerType {
        if (!self.isGameOver()) {
            var next = if (self.last_move_player == PlayerType.black_piece)
                PlayerType.white_piece
            else
                PlayerType.black_piece;
            if (self.history_forwards.items.len == 0) {
                if (self.canMove(self.board, next)) {
                    return next;
                } else {
                    return self.last_move_player;
                }
            } else {
                if (self.player1.is_human and next == PlayerType.black_piece) {
                    return PlayerType.black_piece;
                }
                if (self.player2.is_human and next == PlayerType.white_piece) {
                    return PlayerType.white_piece;
                }
                return null;
            }
        } else {
            return null;
        }
    }

    fn gameEvaluator(self: *Game, board: Board, player: PlayerType) isize {
        var score: isize = 0;

        var opponent = @intFromEnum(if (player == PlayerType.black_piece)
            PlayerType.white_piece
        else
            PlayerType.black_piece);

        var player_int = @intFromEnum(player);

        for (board, 0..) |row, y| {
            for (row, 0..) |square, x| {
                var square_int = @intFromEnum(square);

                if (square_int == player_int) {
                    score += self.heuristic_values[y][x];
                } else if (square_int == opponent) {
                    score -= self.heuristic_values[y][x];
                }
            }
        }
        return score;
    }

    pub fn bestMinimaxMove(self: *Game, player: PlayerType) !Movement {
        var moves = try self.getPossibleMoves(self.allocator, self.board, player);
        defer moves.deinit();

        nodes = 0;

        var score: isize = std.math.minInt(isize);
        var best_move: Movement = undefined;
        for (moves.items) |move| {
            var arena = std.heap.ArenaAllocator.init(self.allocator);
            defer arena.deinit();
            var alloc = arena.allocator();

            var tmp: Board = undefined;

            try self.copyBoard(&tmp, self.board, alloc);

            defer Game.deinitBoard(tmp, alloc);

            var move_score = try self.minimaxSolver(
                7,
                std.math.minInt(isize),
                std.math.maxInt(isize),
                move,
                player,
                &tmp,
                alloc,
            );

            if (move_score > score) {
                score = move_score;
                best_move = move;
            }
        }

        std.debug.print("{d} nodes visited\n", .{nodes});
        return best_move;
    }

    fn minimaxSolver(self: *Game, depth: usize, alpha_mm: isize, beta_mm: isize, move: Movement, player: PlayerType, board: *Board, allocator: mem.Allocator) !isize {
        nodes += 1;
        try self.makeMoveBoard(board, move, allocator);

        if (depth == 0) {
            return self.gameEvaluator(board.*, move.player);
        } else if (self.boardGameOver(board.*)) {
            return std.math.maxInt(isize);
        }
        var alpha = alpha_mm;
        var beta = beta_mm;

        const max = @intFromEnum(move.player) == @intFromEnum(player);

        const opponent = if (player == PlayerType.black_piece)
            PlayerType.white_piece
        else
            PlayerType.black_piece;

        if (!max and !self.canMove(board.*, opponent)) {
            return try self.minimaxSolver(depth - 1, alpha, beta, move, player, board, allocator);
        }
        if (max and !self.canMove(board.*, player)) {
            return try self.minimaxSolver(depth - 1, alpha, beta, move, opponent, board, allocator);
        }

        var total_score: isize = undefined;
        if (max) {
            total_score = std.math.minInt(isize);
            var moves = try self.getPossibleMoves(allocator, board.*, opponent);
            defer moves.deinit();
            for (moves.items) |move_board| {
                var tmp: Board = undefined;
                try self.copyBoard(&tmp, board.*, allocator);
                defer Game.deinitBoard(tmp, allocator);

                var score = try self.minimaxSolver(depth - 1, alpha, beta, move_board, opponent, &tmp, allocator);
                total_score = @max(score, total_score);
                alpha = @max(score, alpha);
                if (beta <= alpha) {
                    break;
                }
            }
        } else {
            total_score = std.math.maxInt(isize);
            var moves = try self.getPossibleMoves(allocator, board.*, player);
            defer moves.deinit();
            for (moves.items) |move_board| {
                var tmp: Board = undefined;
                try self.copyBoard(&tmp, board.*, allocator);
                defer Game.deinitBoard(tmp, allocator);

                var score = try self.minimaxSolver(depth - 1, alpha, beta, move_board, player, &tmp, allocator);
                total_score = @min(score, total_score);
                alpha = @min(score, alpha);
                if (beta <= alpha) {
                    break;
                }
            }
        }
        return total_score;
    }

    fn makeMoveBoard(self: *Game, board: *Board, move: Movement, allocator: mem.Allocator) !void {
        const opponent = @intFromEnum(if (move.player == PlayerType.black_piece)
            PlayerType.white_piece
        else
            PlayerType.black_piece);
        var size = self.size;

        const Tuple = struct { isize, isize };
        const square_type = if (move.player == PlayerType.black_piece)
            SquareType.black_square
        else
            SquareType.white_square;
        var tmp: Board = undefined;
        try self.copyBoard(&tmp, board.*, allocator);

        tmp[move.position.y][move.position.x] = square_type;

        defer Game.deinitBoard(tmp, allocator);

        for (comptime [_]Tuple{
            .{ -1, -1 }, .{ -1, 1 }, .{ 1, -1 }, .{ 1, 1 },
            .{ 0, 1 },   .{ 0, -1 }, .{ 1, 0 },  .{ -1, 0 },
        }) |values| {
            const first = values.@"0";
            const second = values.@"1";

            var moves = std.ArrayList(Movement).init(allocator);
            defer moves.deinit();

            var col_index: isize = @max(@as(isize, @intCast(move.position.x)) + first, 0);
            var row_index: isize = @max(@as(isize, @intCast(move.position.y)) + second, 0);
            var offset: usize = 0;

            while ((col_index > 0 and col_index < size) and (row_index > 0 and row_index < size) and @intFromEnum(board.*[@intCast(row_index)][@intCast(col_index)]) == opponent) {
                try moves.append(Movement{
                    .player = move.player,
                    .position = Position{
                        .x = @intCast(col_index),
                        .y = @intCast(row_index),
                    },
                });
                offset += 1;
                col_index += first;
                row_index += second;
            } else if ((col_index > 0 and col_index < size) and (row_index > 0 and row_index < size) and
                @intFromEnum(self.board[@intCast(row_index)][@intCast(col_index)]) == @intFromEnum(move.player) and
                offset > 0)
            {
                for (moves.items) |movement| {
                    tmp[movement.position.y][movement.position.x] = square_type;
                }
            }
        }
        Game.deinitBoard(board.*, allocator);

        try self.copyBoard(board, tmp, allocator);

        return;
    }

    pub fn getNumberOfMoves(self: *Game, board: Board, player: PlayerType) usize {
        var number: usize = 0;
        for (0..self.size) |y| {
            for (0..self.size) |x| {
                if (self.board[y][x] == .void) {
                    if (self.isValidMove(board, Movement{
                        .player = player,
                        .position = Position{
                            .x = x,
                            .y = y,
                        },
                    })) {
                        number += 1;
                    }
                }
            }
        }
        return number;
    }

    pub fn getPossibleMoves(self: *Game, allocator: mem.Allocator, board: Board, player: PlayerType) !std.ArrayList(Movement) {
        var moves = std.ArrayList(Movement).init(allocator);
        for (0..self.size) |y| {
            for (0..self.size) |x| {
                if (self.board[y][x] == .void) {
                    const move = Movement{
                        .player = player,
                        .position = Position{
                            .x = x,
                            .y = y,
                        },
                    };
                    if (self.isValidMove(board, move)) {
                        try moves.append(move);
                    }
                }
            }
        }
        return moves;
    }

    pub fn canMove(self: *Game, board: Board, player: PlayerType) bool {
        return self.getNumberOfMoves(board, player) > 0;
    }

    pub fn isGameOver(self: *Game) bool {
        return self.boardGameOver(self.board);
    }

    fn boardGameOver(self: *Game, board: Board) bool {
        return !self.canMove(board, .black_piece) and !self.canMove(board, .white_piece);
    }

    pub fn printBoard(self: *Game, board: Board) !void {
        _ = self;
        const out = std.io.getStdOut().writer();
        var size = board.len;

        try out.print("\n   ", .{});
        for (0..size) |i| {
            try out.print("{u: ^4}", .{@as(u8, @intCast(i)) + 65});
        }
        try out.print("\n", .{});

        var x_pos: usize = 0;
        var y_pos: usize = 0;
        for (0..(size * 2 + 1)) |y| {
            if (y % 2 == 1 and y != 1) {
                x_pos = 0;
                y_pos += 1;
            }
            for (0..(size * 2 + 1)) |x| {
                if (x == 0 and y % 2 == 1) {
                    try out.print("{d: <2}", .{y_pos + 1});
                }

                if (x == 0 and y % 2 == 0) {
                    try out.print("  ", .{});
                }

                if (x % 2 == 0 and y % 2 == 0) {
                    try out.print("+", .{});
                    continue;
                }
                if (x % 2 == 1 and y % 2 == 0) {
                    try out.print("---", .{});
                    continue;
                }
                if (y % 2 == 1 and x % 2 == 0) {
                    try out.print("|", .{});
                    continue;
                }
                if (y_pos == size or x_pos == size) {
                    continue;
                }

                switch (board[y_pos][x_pos]) {
                    SquareType.black_square => {
                        try out.print(" {u} ", .{'⬤'});
                    },
                    SquareType.white_square => {
                        try out.print(" {u} ", .{'◯'});
                    },
                    SquareType.void => {
                        try out.print("   ", .{});
                    },
                }
                x_pos += 1;
            }

            try out.print("\n", .{});
        }
    }

    fn getLetters() []u8 {}

    pub fn deinit(self: *Game) void {
        Game.deinitBoard(self.board, self.allocator);

        for (self.heuristic_values) |row| {
            self.allocator.free(row);
        }

        self.allocator.free(self.heuristic_values);

        if (self.initial_board) |initial_board| {
            Game.deinitBoard(initial_board, self.allocator);
        }

        self.history_forwards.deinit();
        self.history_backwards.deinit();
    }
};

const Board = [][]SquareType;

test "Player and Square comparison" {
    try testing.expect(@intFromEnum(PlayerType.black_piece) == @intFromEnum(SquareType.black_square));
}

test "Board" {
    const size = 8;
    var board = try testing.allocator.alloc([]SquareType, size);
    defer testing.allocator.free(board);

    // Create rows
    for (0..size) |index| {
        var row = try testing.allocator.alloc(SquareType, size);
        @memset(row, SquareType.void);
        board[index] = row;
    }

    defer {
        for (board) |row| {
            testing.allocator.free(row);
        }
    }
}

test "Game" {
    var allocator = testing.allocator;
    var game = try Game.newGameAI(allocator, 8, Difficulty.easy);
    var result = game.isValidMove(game.board, Movement{ .player = PlayerType.black_piece, .position = Position{ .x = 4, .y = 5 } });
    try testing.expect(result);
    try testing.expect(!game.isGameOver());
    defer game.deinit();
}

test "Game over" {
    var game = try Game.newGameAI(testing.allocator, 8, Difficulty.easy);
    defer game.deinit();
    try game.makeMove(Movement{ .player = PlayerType.black_piece, .position = Position{ .x = 4, .y = 5 } });
    try game.makeMove(Movement{ .player = PlayerType.black_piece, .position = Position{ .x = 3, .y = 2 } });
    try testing.expect(game.isGameOver());
}

test "Odd number should fail" {
    try testing.expectError(error.BadValue, Game.newGameAI(testing.allocator, 9, Difficulty.easy));
}
