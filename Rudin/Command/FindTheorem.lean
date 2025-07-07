import Lean

open Lean
open Lean.Elab
open Lean.Elab.Command

/--
`find_thms "xxx" "yyy" "-zzz" …`
find the theorems whose names contain the strings "xxx" and "yyy", but not "zzz" etc.
-/
syntax (name := findThms) "#find_thms" (str)+ : command

@[command_elab findThms]
def elabFindThms : CommandElab := fun stx => do
  let args := stx[1].getArgs.map fun s =>
    s.isStrLit?
    |>.get!

  let env ← getEnv

  let filter_name := fun (nm: Name) =>
    let nameStr := nm.toString
    let p1 := nameStr.splitOn "."
    let parts := p1.map (fun s => s.splitOn "_")
    ¬ nm.isInternal ∧ args.all fun a =>
      if a.startsWith "-"
      then parts.flatten.all fun p => (a.toSubstring.drop 1).toString ≠ p
      else parts.flatten.any fun p => a = p


  let thms :=
    env.constants.toList.foldl (init := #[]) fun acc (nm, cinfo) =>
      match cinfo with
      | ConstantInfo.thmInfo .. => acc.push (nm, cinfo)
      | _ => acc

  let res := thms.filter (fun (nm, _) => filter_name nm)

  if res.isEmpty then
    logInfo m!"[find_thms] no matching theorems"
  else
    for item in res do
      let info := item.2
      let msg := match info with
      | ConstantInfo.thmInfo val => val.type
      | _ => panic! "unexpected constant info type"
      logInfo m!"{item.1}:\n{msg}"

theorem test_thms_abc : 1 + 1 = 2 := by
  trivial

theorem test_thms_def : 1 + 1 = 2 := by
  trivial



#find_thms "test" "abc"

#find_thms "test" "-def"
