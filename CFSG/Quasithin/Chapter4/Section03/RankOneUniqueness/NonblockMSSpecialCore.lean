module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSElementaryLifts
public import Theory.Frattini.PGroup

/-!
# The original nonblock core is special

The natural center is irreducible even for additive invariant subgroups:
SL₃ acts transitively on its nonzero vectors. The doubled-dual quotient
puts Q' in Z(Q). This derived subgroup is nontrivial, since otherwise Q
would equal its center and could not surject onto the doubled dual.
Consequently Q'=Z(Q). The elementary quotient and the usual Frattini
containment then give Φ(Q)=Z(Q) in the finite configuration.

Both equalities use the original quotient and subtype maps from MSData.
Together with NonblockMSElementaryLifts they provide the special-core,
elementary-lift and self-centralizer inputs to the C.1.35 core argument.
They do not identify Q with O₂(KS). That remaining argument, construction
of MSData and the component geometry, and the terminal representation
exclusion remain with qt-d-1222-rankone-uniqueness-nonblock.

Source: Aschbacher--Smith, C.1.35(1)--(3), printed pp.137--138;
original 4.3.10--11, printed p.617.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private theorem MSData.center_invariant_eq (d : MSData c n) (A : Subgroup G)
    (hAU : A ≤ U c) (hKA : K c ≤ normalizer (A : Set G)) (hA : A ≠ ⊥) :
    A = U c := by
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKU,_,hn,e,he⟩ := hm
  let := hn
  let u : U c ≃* Multiplicative (Fin 3 → d.field.Carrier) :=
    QuotientGroup.quotientBot.symm.trans e
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hA
  let aU : U c := ⟨a,hAU a.property⟩
  have ha0 : (u aU).toAdd ≠ 0 := by
    intro hh
    have h1 : u aU = 1 := Multiplicative.toAdd.injective hh
    exact ha (Subtype.ext (congrArg (fun z : U c => (z : G))
      (u.injective (h1.trans u.map_one.symm))))
  apply le_antisymm hAU
  intro y hy
  let yU : U c := ⟨y,hy⟩
  by_cases hy0 : (u yU).toAdd = 0
  · have h1 : u yU = 1 := Multiplicative.toAdd.injective hy0
    have hY : y = 1 := congrArg Subtype.val (u.injective (h1.trans u.map_one.symm))
    exact hY.symm ▸ A.one_mem
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (u aU).toAdd (u yU).toAdd ha0 hy0
  obtain ⟨k,hk⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) g
  let z : U c := ⟨(k : G)*a*(k : G)⁻¹,
    (mem_normalizer_iff.mp (hKU k.property) a).mp aU.property⟩
  have hz : z = yU := by
    apply u.injective
    apply Multiplicative.toAdd.injective
    have hh := he k aU z rfl
    change (u z).toAdd = Representation.specialLinearNatural 3
      (linearThreeActor d.model k) (u aU).toAdd at hh
    rw [show linearThreeActor d.model k = g from hk] at hh
    exact hh.trans hg
  have hza : (z : G) ∈ A :=
    (mem_normalizer_iff.mp (hKA k.property) a).mp a.property
  rwa [hz] at hza

/-- The derived subgroup of the original Q is its entire natural center. -/
theorem MSData.core_derived_eq_center (d : MSData c n) :
    (_root_.commutator (Q c)).map (Q c).subtype = U c := by
  obtain ⟨p,hp,hk,_,_⟩ := d.exists_elementary_dual_lifts
  let C := (_root_.commutator (Q c)).map (Q c).subtype
  have hCU : C ≤ U c := by
    have h := map_mono (f := (Q c).subtype) (Abelianization.commutator_subset_ker p)
    rw [hk,map_subgroupOf_eq_of_le d.doubleDual.1] at h
    exact h
  have hKC : K c ≤ normalizer (C : Set G) :=
    d.doubleDual.2.1.trans (normalizer_le_normalizer_characteristic_image
      (Q c) (_root_.commutator (Q c)))
  apply d.center_invariant_eq C hCU hKC
  intro hC
  have hc : _root_.commutator (Q c) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (Q c).subtype_injective).mp hC
  have hZ : U c = Q c := by
    change (center (Q c)).map (Q c).subtype = Q c
    rw [(_root_.commutator_eq_bot_iff_center_eq_top (Q c)).mp hc,
      ←MonoidHom.range_eq_map,range_subtype]
  have hker : p.ker = ⊤ := by rw [hk,hZ]; exact subgroupOf_self _
  have ht : p = 1 := MonoidHom.ker_eq_top_iff.mp hker
  let v : Multiplicative
      (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
        Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) :=
    Multiplicative.ofAdd (LinearMap.proj 0,0)
  obtain ⟨q,hq⟩ := hp v
  have hv : v = 1 := hq.symm.trans (by rw [ht]; rfl)
  have hz := congrArg (fun w => w.toAdd.1 (Pi.single 0 1)) hv
  change (1 : d.field.Carrier) = 0 at hz
  exact one_ne_zero hz

/-- In the original finite configuration, Q is special: its Frattini
subgroup, derived subgroup and center coincide. -/
theorem MSData.core_frattini_eq_center [Finite G] (d : MSData c n) :
    (frattini (Q c)).map (Q c).subtype = U c := by
  obtain ⟨p,hp,hk,_,_⟩ := d.exists_elementary_dual_lifts
  have hpQ : IsPGroup 2 (Q c) := by
    apply (isPGroup_pCoreIn 2 (K c)).to_le
    exact le_normalizer_iff_commutator_le_left.mp
      ((K c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))
  let : Fact (IsPGroup 2 (Q c)) := ⟨hpQ⟩
  apply le_antisymm
  · let : Finite (Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier))) :=
      Finite.of_surjective p hp
    have hs : IsElementaryAbelian 2 (Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier))) := by
      refine { toIsMulCommutative := ⟨⟨fun x y => Multiplicative.toAdd.injective
        (add_comm x.toAdd y.toAdd)⟩⟩
               exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
      intro x
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change x.toAdd + x.toAdd = 0
      rw [←two_smul d.field.Carrier,CharTwo.two_eq_zero,zero_smul]
    let := hs
    let : Fact (IsPGroup 2 (Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)))) :=
      ⟨IsElementaryAbelian.isPGroup 2 _⟩
    have h := frattini_le_comap_frattini_of_surjective hp
    rw [frattini_eq_bot_of_isElementaryAbelian (p := 2)
      (R := Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier))), MonoidHom.comap_bot,hk] at h
    have hh := map_mono (f := (Q c).subtype) h
    rwa [map_subgroupOf_eq_of_le d.doubleDual.1] at hh
  · rw [←d.core_derived_eq_center]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

end
