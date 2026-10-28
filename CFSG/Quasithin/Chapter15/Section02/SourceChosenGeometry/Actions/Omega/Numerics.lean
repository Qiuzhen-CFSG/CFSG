module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Omega.CommonImage
/-!
# The fixed line and plane centralizer in the natural Omega row

The actual Sylow image has order four and exponent two, as follows from
its symmetric-three product isomorphism. If its fixed space were a plane,
it would be an offender on the chosen four-space. The no-FF hypothesis
excludes this, leaving exactly the central-involution line. The action on
the common plane fixes this line and has image of order two, so the literal
centralizer in T has index two.

Source: Aschbacher--Smith 15.2.14(2), printed p.1112, refs/quasithin.pdf.
The preceding source inputs remain with qt-e-152-plane-geometry.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Omega
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 Cyclic
variable {G : Type*} [Group G] [Finite G]
private theorem seed_eq_module_centralizer {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M) :
    centralInvolutions T = V ⊓ centralizer ((T : Subgroup G) : Set G) := by
  let := h.prepared.elementary
  apply le_antisymm
  · exact le_inf (by rw [hfull]; exact le_conjugateSpanBy _ _)
      (centralInvolutions_le_centralizer_sylow T)
  · intro v hv
    exact (mem_omegaOneCenterAmbient_iff _ v).mpr
      ⟨h.le_sylow hv.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv.1,
        fun t ht => hv.2 t ht⟩

/-- A source plane with a seed of order two has centralizer of index two in T. -/
theorem Preceding.plane_index_of_seed_two {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hZ : Nat.card (centralInvolutions T) = 2)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2 := by
  let := h.prepared.elementary
  let E := ⁅V,B⁆
  have hEV : E ≤ V := (d.planes B hB).2.2.1
  have hE : Nat.card E = 4 := (d.planes B hB).2.2.2.1
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) := (d.planes B hB).2.2.2.2.2.1
  have hZE : centralInvolutions T ≤ E := seed_le_commutator h d.full
    (d.actor_le_sylow hB) (d.planes B hB).1 (d.planes B hB).2.1
  obtain ⟨z,hz,hzne⟩ := (centralInvolutions T).bot_or_exists_ne_one.resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
  let f := actionHom (T : Subgroup G) E hTN
  have hfix : ∀ a ∈ f.range, a (⟨z,hZE hz⟩ : E) = ⟨z,hZE hz⟩ := by
    rintro a ⟨t,rfl⟩
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    rw [(centralInvolutions_le_centralizer_sylow T hz) t t.property,mul_inv_cancel_right]
  have hle := card_mulAut_subgroup_le_two_of_fixed_point hE (⟨z,hZE hz⟩ : E)
    (fun he => hzne (congrArg Subtype.val he)) f.range hfix
  have hne : f.range ≠ ⊥ := by
    intro he
    have hET : E ≤ centralizer ((T : Subgroup G) : Set G) := by
      intro v hv t ht
      have ht1 : f ⟨t,ht⟩ = 1 := (show f ⟨t,ht⟩ ∈ (⊥ : Subgroup (MulAut E)) from
        he ▸ (show f ⟨t,ht⟩ ∈ f.range from ⟨⟨t,ht⟩,rfl⟩))
      have hh := congrArg (fun a : MulAut E => (a ⟨v,hv⟩ : G)) ht1
      change t * v * t⁻¹ = v at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hEZ : E ≤ centralInvolutions T := by
      rw [seed_eq_module_centralizer h d.full]
      exact le_inf hEV hET
    have hh := card_le_of_le hEZ
    rw [hE,hZ] at hh
    omega
  have hc : Nat.card f.range = 2 := by
    have hgt := (one_lt_card_iff_ne_bot (H := f.range)).mpr hne
    omega
  have hk : f.ker = (planeCentralizer T E).subgroupOf (T : Subgroup G) := by
    rw [show f = actionHom (T : Subgroup G) E hTN from rfl,actionHom_ker]
    ext t
    exact ⟨fun ht => ⟨t.property,ht⟩,fun ht => ht.2⟩
  change ((planeCentralizer T E).subgroupOf (T : Subgroup G)).index = 2
  rw [←hk,index_ker,hc]


private theorem symmetricThree_fourth (a : Equiv.Perm (Fin 3)) (h : a^4=1) : a^2=1 :=
  (show ∀ a : Equiv.Perm (Fin 3), a^4=1 → a^2=1 from by decide +kernel) a h

/-- The actual Sylow image in the natural Omega row is an elementary four-group. -/
theorem Preceding.sylow_image_four {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    IsElementaryTwo (actor M V (T : Subgroup G) h.prepared.normalized) ∧
      Nat.card (actor M V (T : Subgroup G) h.prepared.normalized) = 4 := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let P : Sylow 2 D := (T.subtype h.maximal.1.2).mapSurjective
    (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  obtain ⟨e⟩ := d.omega.2.2.2.1
  have hc : Nat.card D = 36 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hp : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity,hc]
    decide +kernel
  let : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hp
  change IsElementaryTwo (P : Subgroup D) ∧ Nat.card P = 4
  refine ⟨⟨?_,{ toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }⟩,hp⟩
  · intro he
    have hh : Nat.card P = 1 := by rw [he]; simp
    omega
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply Subtype.ext
    apply e.injective
    change e ((a : D)^2) = e 1
    rw [map_pow,map_one]
    have ha : (e (a : D)) ^ 4 = 1 := by
      rw [←map_pow]
      simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_one] using
        congrArg e (congrArg Subtype.val (show a^4=1 from hp ▸ pow_card_eq_one' (x := a)))
    exact Prod.ext (symmetricThree_fourth _ (congrArg Prod.fst ha))
      (symmetricThree_fourth _ (congrArg Prod.snd ha))

omit [Finite G] in
private theorem ambientSpace_card {V : Subgroup G} [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) : Nat.card (ambientSpace V W) = Nat.card W := by
  rw [ambientSpace,card_map_of_injective V.subtype_injective]
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
    invFun := fun v => ⟨v.val.toMul,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The no-FF condition prevents the Sylow four-group from fixing a plane;
the actual central involutions therefore form a line. -/
theorem Preceding.seed_card {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) : Nat.card (centralInvolutions T) = 2 := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  let P := actor M V (T : Subgroup G) h.prepared.normalized
  obtain ⟨hPe,hPc⟩ := d.sylow_image_four
  have hz := seed_le_commutator h d.full (d.actor_le_sylow hB)
    (d.planes B hB).1 (d.planes B hB).2.1
  have hd : Nat.card (centralInvolutions T) ∣ 2^2 := by
    change Nat.card (centralInvolutions T) ∣ 4
    rw [←(d.planes B hB).2.2.2.1]
    exact card_dvd_of_le hz
  have hge := (one_lt_card_iff_ne_bot (H := centralInvolutions T)).mpr
    (centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
  have hne : Nat.card (centralInvolutions T) ≠ 4 := by
    intro hc
    have hfix : Nat.card (fixedSpace ρ P) = 4 := by
      rw [←ambientSpace_card,ambientSpace_fixed _ h.maximal.1.2,
        ←seed_eq_module_centralizer h d.full]
      exact hc
    have hdim : Module.finrank (ZMod 2) (fixedSpace ρ P) = 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hfix
      exact Nat.pow_right_injective (by decide : 1 < 2) hfix
    have hr : rank P = 2 := by
      change Nat.log 2 (Nat.card P) = 2
      rw [show Nat.card P = 4 from hPc]
      decide
    apply h.not_ff
    refine ⟨P,hPe,?_⟩
    have hh := fixedCodim_add_finrank ρ P
    rw [h.finrank_eq_four,hdim] at hh
    change fixedCodim ρ P ≤ rank P
    rw [hr]
    omega
  obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases n
  · norm_num only [pow_zero] at he
    exact (Nat.ne_of_gt hge he).elim
  · exact he
  · exact (hne he).elim

/-- Both exact numerical clauses of the index-two alternative in 15.2.14(2). -/
theorem Preceding.plane_numerics {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    centralInvolutions T ≤ ⁅V,B⁆ ∧ Nat.card (centralInvolutions T) = 2 ∧
      (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2 :=
  ⟨seed_le_commutator h d.full (d.actor_le_sylow hB)
    (d.planes B hB).1 (d.planes B hB).2.1,
    d.seed_card hB,d.plane_index_of_seed_two (d.seed_card hB) hB⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Omega
