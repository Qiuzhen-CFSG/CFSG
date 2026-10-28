module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.IrreduciblePair
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingPair

/-!
# Source Sp4 pair from the actual moving Sylow actor

An elementary subgroup in the standard Sylow, setwise normalized by a genuine
diagram-moving actor, lies in the actual Sylow center. If it is noncyclic, the
actor rules out both root axes and all diagonal lines. Its opposite pair is
therefore F-irreducible with trivial two-core. This discharges the placement
and irreducibility inputs of E.2.7, pp.219–220, on the same V and group action.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem source_moving_pair {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (a:ActorReduction.stabilizer (F:=F)) (ha:¬PreservesDiagram a.val)
    (V:Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU:V≤unipotent)
    (hV:V.map a.val.toMonoidHom=V) (hr:2<Nat.card V) :
    V≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype ∧
    Representation.IsIrreducible (pairAction V) ∧ pCore 2 (oppositePair V)=⊥ := by
  have hc:=elementary_le_center_of_moving_actor hF hn a.val a.property ha V hVU hV
  have hq : 2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  have hne : V≠⊥ := by intro he; subst V; simp at hr
  obtain ⟨hl,hs⟩:=not_root_axes_of_moving_actor hq a ha V hV hne
  exact ⟨hc,source_pair_irreducible_and_twoCore V hc hl hs
    (not_diagonal_of_moving_actor hq a ha V hV hr)⟩

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
