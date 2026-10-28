module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Defs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Literal binary source hypotheses for MS93

The parabolics are inverse images of the two genuine flag stabilizers in
SL₃(2), under one specified quotient map. A flag conjugation selects their
common Sylow while preserving the quotient marking. `BinaryWeakBN` spells
out the source clauses for these matrix subgroups, taking P_i^* = P_i.
It does not use the legacy `WeakBNPair`.

`LocalSource` is an honest conditional interface: constructing it from the
original input and the characteristic reduction remains a separate obligation.
It does not say that the reduced edge group is an odd-index radical, and it
contains no center, exponent, module-shape or critical-distance conclusion.
The two residual operations in `rankOne` are deliberately in source order.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.827--828, 859, 881.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93

open Subgroup

universe u
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

/-- The two stabilizers of one actual incident flag. -/
def modelParabolic (g : SL) (i : Bool) : Subgroup SL :=
  (if i then Matrix.PSL3Two.lineParabolicSL else Matrix.PSL3Two.pointParabolicSL).map
    (MulAut.conj g).toMonoidHom

def modelBorel (g : SL) : Subgroup SL := modelParabolic g false ⊓ modelParabolic g true

/-- The source WBN clauses on the actual binary quotient; the distinguished
normal subgroup P_i^* is all of P_i in this case. -/
structure BinaryWeakBN (g : SL) : Prop where
  generation : modelParabolic g false ⊔ modelParabolic g true = ⊤
  faithful : ∀ N : Subgroup SL, N.Normal → N ≤ modelBorel g → N = ⊥
  local_characteristic : ∀ i,
    centralizer (pCore 2 (modelParabolic g i) : Set (modelParabolic g i)) ≤
      pCore 2 (modelParabolic g i)
  rank_one : ∀ i, Nonempty
    (((modelParabolic g i) ⧸ pCore 2 (modelParabolic g i)) ≃* SL2)
  borel_normalizer : ∀ i, ∃ S : Sylow 2 (modelParabolic g i),
    (normalizer (S : Set (modelParabolic g i))).map (modelParabolic g i).subtype =
      modelBorel g

variable {M : Type u} [Group M]

/-- Both parabolic preimages use exactly the same marked quotient. -/
def parabolic (π : M →* SL) (g : SL) (i : Bool) : Subgroup M :=
  (modelParabolic g i).comap π

/-- O²(O^{2′}(P)), included into the original group in source order. -/
def rankOne (P : Subgroup M) : Subgroup M :=
  ((pResidual 2 (primeToResidual 2 P)).map (primeToResidual 2 P).subtype).map P.subtype

/-- The characteristic-minimality clause of source 4.0, isolated from its
later assumptions b > 2 and G_alpha/C_alpha ≃ SL₃(2). -/
def CharacteristicMinimal (L R : Subgroup M) : Prop :=
  ∀ A : Subgroup R, A.Characteristic →
    (L ⊔ A.map R.subtype) ⊓ pCore 2 M ≤ A.map R.subtype → A = ⊤

/-- Binary source data on the reduced group. Source E is O₂(M), so its
condition (A) requires no extra extension hypothesis. The equality of the
rank-one generators with the component is retained as a proof obligation. -/
structure LocalSource (L R : Subgroup M) where
  two_group : IsPGroup 2 R
  core_le : pCore 2 M ≤ R
  characteristic : MSCharacteristicCondition R
  product : ∀ m : M, ∃ l ∈ L, ∃ r ∈ R, l * r = m
  residual : pResidual 2 M = L
  minimal : CharacteristicMinimal L R
  projection : M →* SL
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker = pCore 2 M
  flag : SL
  edge_in_borel : R ≤ (modelBorel flag).comap projection
  weakBN : BinaryWeakBN flag
  rank_one_generation :
    rankOne (parabolic projection flag false) ⊔
      rankOne (parabolic projection flag true) = L

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
