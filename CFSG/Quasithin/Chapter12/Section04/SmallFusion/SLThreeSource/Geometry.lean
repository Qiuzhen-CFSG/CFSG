module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Earlier
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.TwoMaximal

/-!
# Local inputs to the original L₃(2) Sylow-centralizer argument

The source plane E lies in the original V, and R₁ is literally C_T(E).
The local calculations below concern Ω₁Z(C_T(V)), the fixed plane, and a
Sylow subgroup of M∩C_G(v). They do not assert an ambient Sylow subgroup,
normalizer containment or fusion. Their construction is the remaining
12.4.5 and initial 12.4.6 calculation.

Source: Aschbacher–Smith, 12.4.5–6, printed pp.813–814. The product in
12.4.5(2) uses the whole V, not merely C_V(L).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source residual O²(C_L(E)), embedded by the literal inclusion. -/
abbrev lineResidual (L E : Subgroup G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer (E : Set G) : Subgroup G)).map
    (L ⊓ centralizer (E : Set G)).subtype

/-- Precisely the local calculations preceding the two escaping-normalizer
cases. The global Sylow and fusion conclusions are absent. -/
structure LocalGeometry {T : Sylow 2 G} {L V : Subgroup G}
    (_D : ChosenModule T L V) where
  E : Subgroup G
  le_module : E ≤ V
  card_plane : Nat.card E = 4
  v : G
  mem_plane : v ∈ E
  nonfixed : v ∉ fixedSubgroup L V
  fixed_supplement : omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
    (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V
  fixed_plane : V ⊓ centralizer
    (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) = E
  index : ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2
  local_sylow : Chapter1.IsSylowIn 2
    ((T : Subgroup G) ⊓ centralizer (E : Set G))
    (normalizer (L : Set G) ⊓ centralizer ({v} : Set G))

namespace LocalGeometry
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

/-- The original subgroup R₁=C_T(E). -/
abbrev R : Subgroup G := (T : Subgroup G) ⊓ centralizer (d.E : Set G)

/-- The original L₁=O²(C_L(E)). -/
abbrev L₁ : Subgroup G := lineResidual L d.E

omit [Finite G] in
theorem sylow_normalizes : (T : Subgroup G) ≤ normalizer (d.R : Set G) := by
  let : (d.R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two d.index
  exact le_normalizer_of_normal_subgroupOf (show d.R ≤ (T : Subgroup G) from inf_le_left)

include d in
/-- The fixed-line calculation follows from the local Sylow witness and
the already proved transitivity outside C_V(L). A nonfixed central vector
would conjugate the whole T into M∩C_G(v), contradicting its Sylow order. -/
theorem fixed_line
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    omegaCenterIn (T : Subgroup G) ⊓ V = fixedSubgroup L V := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  obtain ⟨_, z, _, hgen, _, _, hzZ, _⟩ := exists_slThree_fixed_involution_setup
    h D structural marked uniquenessEarlier_knownSimple hmodel hne
  have hFZ : fixedSubgroup L V ≤ omegaCenterIn (T : Subgroup G) := by
    rw [hgen, omegaCenterIn_eq_omegaOneAmbient]
    exact zpowers_le_of_mem hzZ
  apply le_antisymm ?_ (le_inf hFZ inf_le_left)
  intro x hx
  by_contra hxf
  obtain ⟨l, hl, hlx⟩ := ext.transitive_nonfixed hne x d.v
    hx.2 (d.le_module d.mem_plane) hxf d.nonfixed
  let M := normalizer (L : Set G)
  let C := M ⊓ centralizer ({d.v} : Set G)
  have hlM : l ∈ M := L.le_normalizer hl
  let f : T →* C :=
    ((MulAut.conj l).toMonoidHom.comp (T : Subgroup G).subtype).codRestrict C (by
      intro t
      refine ⟨?_, ?_⟩
      · exact M.mul_mem (M.mul_mem hlM ((structural G T L h).1 t.property))
          (M.inv_mem hlM)
      · apply mem_centralizer_singleton_iff.mpr
        rw [← hlx]
        exact (MulAut.conj l).map_mul (t : G) x |>.symm.trans
          ((congrArg (MulAut.conj l)
            (((mem_omegaCenterIn_iff _ _).mp hx.1).2.1 t t.property)).trans
              ((MulAut.conj l).map_mul x (t : G))))
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext ((MulAut.conj l).injective (congrArg Subtype.val he))
  obtain ⟨P, hP⟩ := d.local_sylow
  change (P : Subgroup C).map C.subtype = d.R at hP
  obtain ⟨Q, hQ⟩ :=
    (T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hc : Nat.card T ≤ Nat.card d.R := by
    calc
      Nat.card T = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
      _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
      _ = Nat.card P := Nat.card_congr (Q.equiv P).toEquiv
      _ = Nat.card d.R := by
        rw [← hP]
        exact Nat.card_congr
          ((P : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).toEquiv
  have he : d.R = (T : Subgroup G) := eq_of_le_of_card_ge inf_le_left hc
  have hi := d.index
  change d.R.relIndex (T : Subgroup G) = 2 at hi
  simp [he] at hi

/-- The known-simple source specializes the previously proved omega and
index-three calculation, discharging its uniqueness premise. -/
theorem escape_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) = fixedSubgroup L V ∧
    Nat.card (omegaCenterIn (T : Subgroup G)) = 2 ∧
    d.E = omegaCenterIn d.R ∧
    normalizer (d.R : Set G) ≤ normalizer (d.E : Set G) ∧
    (normalizer (L : Set G) ⊓ normalizer (d.R : Set G)).relIndex
      (normalizer (d.R : Set G)) = 3 :=
  escaping_normalizer_four_group h D structural marked uniquenessEarlier_knownSimple
    hmodel hne d.E d.le_module d.card_plane d.fixed_supplement
    (d.fixed_line h structural marked hmodel hne)
    d.fixed_plane d.index hescape

omit [Finite G] in
/-- M∩N_G(R₁) normalizes the literal O²(C_L(E)) once N_G(R₁) normalizes E. -/
theorem intersection_normalizes_lineResidual
    (hNE : normalizer (d.R : Set G) ≤ normalizer (d.E : Set G)) :
    normalizer (L : Set G) ⊓ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ centralizer (d.E : Set G)) (pResidual 2 _))
  exact (le_inf inf_le_left
    (inf_le_right.trans (hNE.trans (normalizer_le_normalizer_centralizer d.E)))).trans
      inf_normalizer_le_normalizer_inf

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
