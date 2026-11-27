import Lean
open Lean Elab Command
namespace CategoryTheory.Abelian
def Ext := Nat
namespace Ext
def instAddCommGroup := 0
def comp := 0
def mk₀ := 0
def homEquiv := 0
def mapExactFunctor := 0
end Ext
end CategoryTheory.Abelian

macro "sealAbelianExt" : command =>
  `(seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
    CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
    CategoryTheory.Abelian.Ext.mapExactFunctor)

open CategoryTheory.Abelian in
private def flagsMatch (expected : Lean.ReducibilityStatus) : CommandElabM Unit := do
  for n in [``Ext, ``Ext.instAddCommGroup, ``Ext.comp, ``Ext.mk₀, ``Ext.homEquiv, ``Ext.mapExactFunctor] do
    unless (← getReducibilityStatus n) == expected do throwError "wrong reducibility flag for {n}"

run_cmd flagsMatch .semireducible
sealAbelianExt in
run_cmd flagsMatch .irreducible
run_cmd flagsMatch .semireducible
sealAbelianExt
run_cmd flagsMatch .irreducible
