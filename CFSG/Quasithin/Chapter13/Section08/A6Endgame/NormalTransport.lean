module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.MarkedParabolic
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionTransport
public import Theory.GroupTheory.PCoreImage

/-!
# Relative marked cores in the terminal point parabolic

This is the containment argument in the last paragraph of Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
§13.8, printed pp.968–969 (PDF pp.985–986).

In the S₆ point parabolic C₂ × S₄, a strict normal extension of a normal
subgroup of order two contains the entire two-core. A relatively normal
marked subgroup therefore has its two-core in that extension. In the A₆
point parabolic S₄, a normal subgroup of order two is already impossible.
This proves the required marked containment without assuming that the
marked subgroup maps to a particular A₄. Both normalities are local to
the point parabolic, never normality in the ambient simple group.

The action comparison is an equivariant embedding of the duad orbit.
It applies to a distinguished orbit inside a cover module without equating
its full set of vectors with the fifteen nonzero vectors of the natural
module. The embedding and its equivariance are still explicit inputs: this
module does not construct the source module identification or identify an
outer twist from the dimension. The point transporter h acts by inverse
conjugation in the model; the separate conjugator c carries the γ subgroups
to the α marking.

Theorems 13.8.33–34 and the source action/geometry inputs remain obligations
of their owners. The contradiction theorems here consume the strict
containment from 13.8.11(1), order two from 13.8.34(2), and noncontainment
from 13.8.34(3); they do not prove those premises.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame

open Subgroup Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.DuadCalculation

/-- An equivariant embedding identifies the stabilizer of a point in its
image. Surjectivity onto all vectors is unnecessary for a cover module. -/
theorem stabilizer_transport_of_embedding {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] (e : G ≃* H) (i : Y → X)
    (hi : Function.Injective i) (heq : ∀ g y, i (e g • y) = g • i y) (y : Y) :
    (MulAction.stabilizer G (i y)).map e.toMonoidHom = MulAction.stabilizer H y := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    change e g • y = y
    apply hi
    rw [heq]
    exact hg
  · intro hh
    obtain ⟨g, rfl⟩ := e.surjective h
    refine mem_map.mpr ⟨g, ?_, rfl⟩
    change g • i y = i y
    rw [← heq]
    exact congrArg i hh

noncomputable def stabilizerModelOfEmbedding {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] (e : G ≃* H) (i : Y → X)
    (hi : Function.Injective i) (heq : ∀ g y, i (e g • y) = g • i y) (y : Y) :
    MulAction.stabilizer G (i y) ≃* MulAction.stabilizer H y :=
  (e.subgroupMap _).trans
    (MulEquiv.subgroupCongr (stabilizer_transport_of_embedding e i hi heq y))

/-- Only the specified orbit is identified with duads. The carrier `X` may
be the full cover module, and the choice of the natural action remains explicit. -/
noncomputable def embeddedDuadPointModel {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* S6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : S6) :
    MulAction.stabilizer G (i (h • (0 : Duad))) ≃* duadStabilizer :=
  (stabilizerModelOfEmbedding e i hi heq _).trans (duadStabilizerModel _ h rfl)

noncomputable def embeddedEvenDuadPointModel {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* A6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : A6) :
    MulAction.stabilizer G (i (h • (0 : Duad))) ≃* a6DuadStabilizer :=
  (stabilizerModelOfEmbedding e i hi heq _).trans (evenDuadStabilizerModel _ h rfl)

/-- The transporter acts by inverse conjugation, after the given action
isomorphism. It cannot be silently replaced by the transporter to α. -/
theorem embeddedDuadPointModel_apply {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* S6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : S6)
    (z : MulAction.stabilizer G (i (h • (0 : Duad)))) :
    (embeddedDuadPointModel e i hi heq h z).val = MulAut.conj h⁻¹ (e z.val) := by
  exact MulAction.stabilizerEquivStabilizer_symm_apply
    (show h • (0 : Duad) = h • (0 : Duad) from rfl).symm _

theorem embeddedEvenDuadPointModel_apply {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* A6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : A6)
    (z : MulAction.stabilizer G (i (h • (0 : Duad)))) :
    (embeddedEvenDuadPointModel e i hi heq h z).val = MulAut.conj h⁻¹ (e z.val) := by
  exact MulAction.stabilizerEquivStabilizer_symm_apply
    (show h • (0 : Duad) = h • (0 : Duad) from rfl).symm _

theorem twoCore_le_of_normal_pair_model {P : Type*} [Group P]
    (model : Nonempty (P ≃* a6DuadStabilizer) ∨ Nonempty (P ≃* duadStabilizer))
    (U V : Subgroup P) [U.Normal] [V.Normal]
    (hU : Nat.card U = 2) (hlt : U < V) : pCore 2 P ≤ V := by
  rcases model with h | h
  · obtain ⟨e⟩ := h
    let f := e.trans a6DuadModelEquiv.symm
    have : (U.map f.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ f.surjective
    exact (four_normal_card_ne_two (U.map f.toMonoidHom)
      ((Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective).trans hU)).elim
  · obtain ⟨e⟩ := h
    let f := e.trans duadProductEquiv.symm
    have : (U.map f.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ f.surjective
    have : (V.map f.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ f.surjective
    have hh := twoCore_le_of_strict_normal_pair (U.map f.toMonoidHom) (V.map f.toMonoidHom)
      ((Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective).trans hU)
      (f.mapSubgroup.strictMono hlt)
    rw [← pCore_map_iso 2 f] at hh
    intro x hx
    obtain ⟨y, hy, he⟩ := hh (mem_map.mpr ⟨x, hx, rfl⟩)
    exact f.injective he ▸ hy

theorem twoCore_le_of_relative_normal_pair {G : Type*} [Group G] (P U V : Subgroup G)
    (model : Nonempty (P ≃* a6DuadStabilizer) ∨ Nonempty (P ≃* duadStabilizer))
    (hVP : V ≤ P) (hUn : P ≤ normalizer (U : Set G))
    (hVn : P ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) : P.pCoreIn 2 ≤ V := by
  have hUP : U ≤ P := hlt.le.trans hVP
  have : (U.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUP).mpr hUn
  have : (V.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVP).mpr hVn
  have hU' : Nat.card (U.subgroupOf P) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv).trans hU
  have hlt' : U.subgroupOf P < V.subgroupOf P := by
    apply lt_of_le_of_ne
    · intro x hx
      exact hlt.le hx
    · intro he
      have := congrArg (Subgroup.map P.subtype) he
      rw [map_subgroupOf_eq_of_le hUP, map_subgroupOf_eq_of_le hVP] at this
      exact hlt.ne this
  have hm := Subgroup.map_mono (f := P.subtype)
    (twoCore_le_of_normal_pair_model model (U.subgroupOf P) (V.subgroupOf P) hU' hlt')
  rwa [map_subgroupOf_eq_of_le hVP] at hm

theorem normal_marked_core_le {G : Type*} [Group G] (P J U V : Subgroup G)
    (model : Nonempty (P ≃* a6DuadStabilizer) ∨ Nonempty (P ≃* duadStabilizer))
    (hJP : J ≤ P) (hVP : V ≤ P) (hJn : P ≤ normalizer (J : Set G))
    (hUn : P ≤ normalizer (U : Set G)) (hVn : P ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) : J.pCoreIn 2 ≤ V :=
  (pCoreIn_mono_of_normalizes hJP hJn).trans
    (twoCore_le_of_relative_normal_pair P U V model hVP hUn hVn hU hlt)

theorem normal_marked_conjugate_contradiction {G : Type*} [Group G]
    (P J Ug Vg Va Ja : Subgroup G) (c : G)
    (model : Nonempty (P ≃* a6DuadStabilizer) ∨ Nonempty (P ≃* duadStabilizer))
    (hJP : J ≤ P) (hVP : Vg ≤ P) (hJn : P ≤ normalizer (J : Set G))
    (hUn : P ≤ normalizer (Ug : Set G)) (hVn : P ≤ normalizer (Vg : Set G))
    (hU : Nat.card Ug = 2) (hlt : Ug < Vg)
    (hVa : Vg.map (MulAut.conj c).toMonoidHom = Va)
    (hJa : J.map (MulAut.conj c).toMonoidHom = Ja)
    (hnot : ¬ Ja.pCoreIn 2 ≤ Va) : False := by
  apply hnot
  have hm := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom)
    (normal_marked_core_le P J Ug Vg model hJP hVP hJn hUn hVn hU hlt)
  rwa [map_pCoreIn_of_injective 2 J _ (MulAut.conj c).injective, hJa, hVa] at hm

/-- The final marked containment under an explicitly compatible S₆ action.
In a source application `J` is the conjugated `L₁*`, and `U,V` are `Uγ*,Vγ*`.
The relative normality of `J` suffices; its image need not be supplied as A₄. -/
theorem s6_embedded_point_marked_core_le {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* S6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : S6) (J U V : Subgroup G)
    (hJP : J ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hVP : V ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hJn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (J : Set G))
    (hUn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (U : Set G))
    (hVn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) : J.pCoreIn 2 ≤ V :=
  normal_marked_core_le _ J U V (Or.inr ⟨embeddedDuadPointModel e i hi heq h⟩)
    hJP hVP hJn hUn hVn hU hlt

/-- The same containment for the separately specified A₆ action. -/
theorem a6_embedded_point_marked_core_le {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* A6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : A6) (J U V : Subgroup G)
    (hJP : J ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hVP : V ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hJn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (J : Set G))
    (hUn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (U : Set G))
    (hVn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) : J.pCoreIn 2 ≤ V :=
  normal_marked_core_le _ J U V (Or.inl ⟨embeddedEvenDuadPointModel e i hi heq h⟩)
    hJP hVP hJn hUn hVn hU hlt

/-- The S₆ final comparison with both conjugators retained: `h` locates
the point parabolic, and `c` moves the γ subgroups to the α marking. -/
theorem s6_embedded_point_contradiction {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* S6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : S6)
    (J Ug Vg Va Ja : Subgroup G) (c : G)
    (hJP : J ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hVP : Vg ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hJn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (J : Set G))
    (hUn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (Ug : Set G))
    (hVn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (Vg : Set G))
    (hU : Nat.card Ug = 2) (hlt : Ug < Vg)
    (hVa : Vg.map (MulAut.conj c).toMonoidHom = Va)
    (hJa : J.map (MulAut.conj c).toMonoidHom = Ja)
    (hnot : ¬ Ja.pCoreIn 2 ≤ Va) : False :=
  normal_marked_conjugate_contradiction _ J Ug Vg Va Ja c
    (Or.inr ⟨embeddedDuadPointModel e i hi heq h⟩)
    hJP hVP hJn hUn hVn hU hlt hVa hJa hnot

/-- The A₆ final comparison, for its explicitly specified action. -/
theorem a6_embedded_point_contradiction {G X : Type*} [Group G] [MulAction G X]
    (e : G ≃* A6) (i : Duad → X) (hi : Function.Injective i)
    (heq : ∀ g d, i (e g • d) = g • i d) (h : A6)
    (J Ug Vg Va Ja : Subgroup G) (c : G)
    (hJP : J ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hVP : Vg ≤ MulAction.stabilizer G (i (h • (0 : Duad))))
    (hJn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (J : Set G))
    (hUn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (Ug : Set G))
    (hVn : MulAction.stabilizer G (i (h • (0 : Duad))) ≤ normalizer (Vg : Set G))
    (hU : Nat.card Ug = 2) (hlt : Ug < Vg)
    (hVa : Vg.map (MulAut.conj c).toMonoidHom = Va)
    (hJa : J.map (MulAut.conj c).toMonoidHom = Ja)
    (hnot : ¬ Ja.pCoreIn 2 ≤ Va) : False :=
  normal_marked_conjugate_contradiction _ J Ug Vg Va Ja c
    (Or.inl ⟨embeddedEvenDuadPointModel e i hi heq h⟩)
    hJP hVP hJn hUn hVn hU hlt hVa hJa hnot

end CFSG.Quasithin.Chapter13.Section08.A6Endgame
