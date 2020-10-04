type Instruction =
    | Mov of int16 * int16
    | Add of int16 * int16
    | Sub of int16 * int16
    | And of int16 * int16
    | Or of int16 * int16
    | Sl of int16
    | Sr of int16
    | Sra of int16
    | Ldl of int16 * int16
    | Ldh of int16 * int16
    | Cmp of int16 * int16
    | Je of int16
    | Jmp of int16
    | Ld of int16 * int16
    | St of int16 * int16
    | Hlt

// Opcode
let MOV = 0s
let ADD = 1s
let SUB = 2s
let AND = 3s
let OR  = 4s
let SL  = 5s
let SR  = 6s
let SRA = 7s
let LDL = 8s
let LDH = 9s
let CMP = 10s
let JE  = 11s
let JMP = 12s
let LD  = 13s
let ST  = 14s
let HLT = 15s

// Register index
let REG0 = 0s
let REG1 = 1s
let REG2 = 2s
let REG3 = 3s
let REG4 = 4s
let REG5 = 5s
let REG6 = 6s
let REG7 = 7s

let reg: int16[] = Array.zeroCreate 8
let rom: int16[] = Array.zeroCreate 256
let ram: int16[] = Array.zeroCreate 256

let mutable pc: int16 = 0s // Program counter
let mutable ir: int16 = 0s // Instrution register
let mutable flagEq: bool = false // Equal comparison flag

let assemble instruction =
    match instruction with
    | Mov (ra, rb) -> (MOV <<< 11) ||| (ra <<< 8) ||| (rb <<< 5)
    | Add (ra, rb) -> (ADD <<< 11) ||| (ra <<< 8) ||| (rb <<< 5)
    | Sub (ra, rb) -> (SUB <<< 11) ||| (ra <<< 8) ||| (rb <<< 5)
    | And (ra, rb) -> (AND <<< 11) ||| (ra <<< 8) ||| (rb <<< 5)
    | Or (ra, rb) -> (OR <<< 11) ||| (ra <<< 8) ||| (rb <<< 5)
    | Sl ra -> (SL <<< 11) ||| (ra <<< 8)
    | Sr ra -> (SR <<< 11) ||| (ra <<< 8)
    | Sra ra -> (SRA <<< 11) ||| (ra <<< 8)
    | Ldl (ra, data) -> (LDL <<< 11) ||| (ra <<< 8) ||| (data &&& 0x00FFs)
    | Ldh (ra, data) -> (LDH <<< 11) ||| (ra <<< 8) ||| (data &&& 0x00FFs)
    | Cmp (ra, rb) -> (CMP <<< 11) ||| (ra <<< 8) ||| (rb <<< 5)
    | Je addr -> (JE <<< 11) ||| (addr &&& 0x00FFs)
    | Jmp addr -> (JMP <<< 11) |||(addr &&& 0x00FFs)
    | Ld (ra, addr) -> (LD <<< 11) ||| (ra <<< 8) ||| (addr &&& 0x00FFs)
    | St (ra, addr) -> (ST <<< 11) ||| (ra <<< 8) ||| (addr &&& 0x00FFs)
    | Hlt -> HLT <<< 11

let getOpcode (ir: int16) = ir >>> 11
let getRegA (ir: int16) = (ir >>> 8) &&& 0x0007s
let getRegB (ir: int16) = (ir >>> 5) &&& 0x0007s
let getData (ir: int16) = ir &&& 0x00FFs
let getAddr (ir: int16) = ir &&& 0x00FFs

let fetch () = rom.[int pc]

let decode ir =
    let opcode = getOpcode ir
    if opcode = MOV then Mov (getRegA ir, getRegB ir)
    elif opcode = ADD then Add (getRegA ir, getRegB ir)
    elif opcode = SUB then Sub (getRegA ir, getRegB ir)
    elif opcode = AND then And (getRegA ir, getRegB ir)
    elif opcode = OR then Or (getRegA ir, getRegB ir)
    elif opcode = SL then Sl (getRegA ir)
    elif opcode = SR then Sr (getRegA ir)
    elif opcode = SRA then Sra (getRegA ir)
    elif opcode = LDL then Ldl (getRegA ir, getData ir)
    elif opcode = LDH then Ldh (getRegA ir, getData ir)
    elif opcode = CMP then Cmp (getRegA ir, getRegB ir)
    elif opcode = JE then Je (getAddr ir)
    elif opcode = JMP then Jmp (getAddr ir)
    elif opcode = LD then Ld (getRegA ir, getAddr ir)
    elif opcode = ST then St (getRegA ir, getAddr ir)
    else Hlt

let execute instruction =
    match instruction with
    | Mov (ra, rb) ->
        reg.[int ra] <- reg.[int rb]
        pc <- pc + 1s
    | Add (ra, rb) ->
        reg.[int ra] <- reg.[int ra] + reg.[int rb]
        pc <- pc + 1s
    | Sub (ra, rb) ->
        reg.[int ra] <- reg.[int ra] - reg.[int rb]
        pc <- pc + 1s
    | And (ra, rb) ->
        reg.[int ra] <- reg.[int ra] &&& reg.[int rb]
        pc <- pc + 1s
    | Or (ra, rb) ->
        reg.[int ra] <- reg.[int ra] ||| reg.[int rb]
        pc <- pc + 1s
    | Sl ra ->
        reg.[int ra] <- reg.[int ra] <<< 1
        pc <- pc + 1s
    | Sr ra ->
        reg.[int ra] <- (reg.[int ra] >>> 1) &&& 0x8000s
        pc <- pc + 1s
    | Sra ra ->
        reg.[int ra] <- reg.[int ra] >>> 1
        pc <- pc + 1s
    | Ldl (ra, data) ->
        reg.[int ra] <- (reg.[int ra] &&& 0xFF00s) ||| (data &&& 0x00FFs)
        pc <- pc + 1s
    | Ldh (ra, data) ->
        reg.[int ra] <- (data <<< 8) ||| (reg.[int ra] &&& 0x00FFs)
        pc <- pc + 1s
    | Cmp (ra, rb) ->
        flagEq <- reg.[int ra] = reg.[int rb]
        pc <- pc + 1s
    | Je addr ->
        pc <- if flagEq then addr else pc + 1s
    | Jmp addr ->
        pc <- addr
    | Ld (ra, addr) ->
        reg.[int ra] <- ram.[int addr]
        pc <- pc + 1s
    | St (ra, addr) ->
        ram.[int addr] <- reg.[int ra]
        pc <- pc + 1s
    | Hlt ->
        ()

let rec loop () =
    ir <- fetch ()
    printfn "pre : %5d %5x %5d %5d %5d %5d" pc ir reg.[0] reg.[1] reg.[2] reg.[3]
    match decode ir with
    | Hlt -> printfn "RAM[64] = %d" ram.[64]
    | inst -> execute inst; loop ()

[<EntryPoint>]
let main argv =
    rom.[0]  <- assemble (Ldh (REG0, 0s))   // 00: REG0(H) <- 0
    rom.[1]  <- assemble (Ldl (REG0, 0s))   // 01: REG0(L) <- 0
    rom.[2]  <- assemble (Ldh (REG1, 0s))   // 02: REG1(H) <- 0
    rom.[3]  <- assemble (Ldl (REG1, 1s))   // 03: REG1(L) <- 1
    rom.[4]  <- assemble (Ldh (REG2, 0s))   // 04: REG2(H) <- 0
    rom.[5]  <- assemble (Ldl (REG2, 0s))   // 05: REG2(L) <- 0
    rom.[6]  <- assemble (Ldh (REG3, 0s))   // 06: REG3(H) <- 0
    rom.[7]  <- assemble (Ldl (REG3, 10s))  // 07: REG3(L) <- 10
    rom.[8]  <- assemble (Add (REG2, REG1)) // 08: REG2 <- REG2 + REG1
    rom.[9]  <- assemble (Add (REG0, REG2)) // 09: REG0 <- REG0 + REG2
    rom.[10] <- assemble (St (REG0, 64s))   // 10: RAM[64] <- REG0
    rom.[11] <- assemble (Cmp (REG2, REG3)) // 11: REG2 == REG3 ?
    rom.[12] <- assemble (Je 14s)           // 12: if equals, jump 14 addres
    rom.[13] <- assemble (Jmp 8s)           // 13: jump 8 address
    rom.[14] <- assemble Hlt                // 14: Halt cpu
    loop ()
    0
