module
public import CFSG.Quasithin.ChapterC.Defs
public import Theory.GroupTheory.SylowNormalIntersectionControl
public import Theory.GroupTheory.CComponent.CommutatorDichotomy
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SylowSubnormalIntersection
/-!
# The original normal-closure Sylow control in C.2.4

The source hypothesis makes Q Sylow in its normal closure inside M. We
retain this exact closure as a subgroup of the original group. Its Sylow
intersection with a normal subgroup controls all normalized two-elements.
A component moved by Q and contained in M lies in that closure, since its
full commutator with Q contains it; hence Q intersects it in a Sylow group.
Finally, a displacement y⁻¹ s y s⁻¹ with y in M and s in Q lies in this
closure and is forced into the original component stabilizer.

Source: Aschbacher–Smith C.2.4(2), printed p.144; Aschbacher, Math. Z. 177
(1981), 10.3, p.78. No Sylow hypothesis on all of M is used.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

@[expose] def radicalClosure (R M : Subgroup G) : Subgroup G :=
  (normalClosure (R.subgroupOf M : Set M)).map M.subtype

omit [Finite G] in
theorem radicalClosure_le (R M : Subgroup G) : radicalClosure R M ≤ M := map_subtype_le _

omit [Finite G] in
theorem normalizes_radicalClosure (R M : Subgroup G) :
    M ≤ normalizer (radicalClosure R M : Set G) := by
  intro m hm
  exact (normalClosure (R.subgroupOf M : Set M)).le_normalizer_map M.subtype
    (mem_map_of_mem M.subtype (le_normalizer_of_normal (mem_top (⟨m,hm⟩ : M))))

theorem closure_sylow {R M : Subgroup G}
    (h : IsSylowInNormalClosure R M) :
    ∃ S : Sylow 2 (radicalClosure R M),
      (S : Subgroup (radicalClosure R M)).map (radicalClosure R M).subtype = R := by
  let N := normalClosure (R.subgroupOf M : Set M)
  obtain ⟨S,hS⟩ := h
  let e : N ≃* radicalClosure R M := N.equivMapOfInjective M.subtype M.subtype_injective
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup N).map e.toMonoidHom).map (radicalClosure R M).subtype = R
  rw [map_map]
  change (S : Subgroup N).map (M.subtype.comp N.subtype) = R
  rwa [← map_map]

theorem radical_le_closure {R M : Subgroup G}
    (h : IsSylowInNormalClosure R M) : R ≤ radicalClosure R M := by
  obtain ⟨S,hS⟩ := closure_sylow h
  exact hS.symm.le.trans (map_subtype_le (S : Subgroup (radicalClosure R M)))

theorem closure_control_in_normal {R M D K : Subgroup G}
    (h : IsSylowInNormalClosure R M) [D.Normal]
    (hKp : IsPGroup 2 K) (hKC : K ≤ radicalClosure R M) (hKD : K ≤ D)
    (hKn : K ≤ normalizer ((R ⊓ D : Subgroup G) : Set G)) : K ≤ R ⊓ D := by
  obtain ⟨S,hS⟩ := closure_sylow h
  exact le_sylow_inf_normal_of_normalizes (radicalClosure R M) D S R K hS hKp hKC hKD hKn

theorem component_le_commutator_of_moved {Q L : Subgroup G}
    (hL : L.IsCComponent) (hm : ¬ Q ≤ normalizer (L : Set G)) : L ≤ ⁅L,Q⁆ := by
  rcases hL.commutator_le_radical_or_eq_iSup_conjugates Q with hh | hh
  · apply False.elim
    apply hm
    let q := QuotientGroup.mk' (solvableRadical G)
    have hc : ⁅L.map q,Q.map q⁆ = ⊥ := by
      rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hh
    have hn : Q.map q ≤ normalizer (L.map q : Set (G ⧸ solvableRadical G)) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hl := map_le_iff_le_comap.mp hn
    rwa [normalizer_cComponent_quotient hL (solvableRadical G)] at hl
  · rw [hh]
    exact le_iSup_conjugates L Q

theorem moved_component_inside_control_sylow {Q M L : Subgroup G}
    (hs : IsSylowInNormalClosure Q M) (hL : L.IsCComponent)
    (hLM : L ≤ M) (hm : ¬ Q ≤ normalizer (L : Set G)) :
    ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = Q ⊓ L := by
  let C := radicalClosure Q M
  have hQC : Q ≤ C := radical_le_closure hs
  have hLC : L ≤ C := (component_le_commutator_of_moved hL hm).trans
    ((commutator_mono le_rfl hQC).trans
      (le_normalizer_iff_commutator_le_right.mp (hLM.trans (normalizes_radicalClosure Q M))))
  obtain ⟨S,hS⟩ := closure_sylow hs
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf C) hL.subnormal.subgroupOf
  let e : L.subgroupOf C ≃* L := subgroupOfEquivOfLe hLC
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((T : Subgroup (L.subgroupOf C)).map e.toMonoidHom).map L.subtype = _
  rw [map_map,hT]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨hS ▸ mem_map_of_mem C.subtype hy,y.property⟩
  · rintro ⟨hxQ,hxL⟩
    let y : L.subgroupOf C := ⟨⟨x,hLC hxL⟩,hxL⟩
    refine ⟨y, ?_, rfl⟩
    change (y : C) ∈ S
    apply (mem_map_iff_mem C.subtype_injective).mp
    rw [hS]
    exact hxQ
end CFSG.Quasithin.ChapterC.Section02Source

namespace CFSG.Quasithin.ChapterC.Section02Source
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem displacement_mem_radical_stabilizer {Q M D : Subgroup G}
    (hs : IsSylowInNormalClosure Q M) [D.Normal]
    (y s : G) (hy : y ∈ M) (hsQ : s ∈ Q)
    (hp : IsPGroup 2 (zpowers (y⁻¹ * (s * y * s⁻¹))))
    (hD : y⁻¹ * (s * y * s⁻¹) ∈ D)
    (hn : y⁻¹ * (s * y * s⁻¹) ∈ normalizer ((Q ⊓ D : Subgroup G) : Set G)) :
    y⁻¹ * (s * y * s⁻¹) ∈ Q ⊓ D := by
  let C := radicalClosure Q M
  have hsC : s ∈ C := radical_le_closure hs hsQ
  have hyC : y⁻¹ * s * (y⁻¹)⁻¹ ∈ C :=
    ((normalizes_radicalClosure Q M (M.inv_mem hy)) s).mp hsC
  have hwC : y⁻¹ * (s * y * s⁻¹) ∈ C := by
    have hh := C.mul_mem hyC (C.inv_mem hsC)
    simpa only [inv_inv,mul_assoc] using hh
  exact closure_control_in_normal hs hp (zpowers_le.mpr hwC)
    (zpowers_le.mpr hD) (zpowers_le.mpr hn) (mem_zpowers _)
end CFSG.Quasithin.ChapterC.Section02Source
