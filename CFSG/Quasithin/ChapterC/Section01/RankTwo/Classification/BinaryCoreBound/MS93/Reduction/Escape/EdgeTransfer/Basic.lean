module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# General binary edge algebra for MS93 (4.2)(i)

The actual marked natural subgroup contains every edge displacement and has
order eight. The edge two-group forces that displacement to have order at
most four. The opposite omega-center is exactly the fixed subgroup in Z.
These arguments use only the source, b > 2, and the preceding module facts.
They use no escape assertion or critical-distance-four conclusions.

Adapted from the independent edge algebra in DistanceFour/Early; the original
modules and their stronger public interfaces are preserved.
Source: Meierfrankenfeld--Stellmacher (1993), (4.1)--(4.2), pp.881--882.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
variable {M : Type*} [Group M] {L R : Subgroup M}

theorem edge_Z_le (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    Z R b ≤ Z R a := by
  have hb : color R b ≠ false := fun hb => (adjacent_color_ne R hab) (ha.trans hb.symm)
  rw [Z, if_neg hb, Z, if_pos ha]
  exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)

theorem fixedCore_normalized (R : Subgroup M) (a : Vertex R) :
    stabilizer R a ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) := by
  rw [le_normalizer_iff]
  intro g hg x hx
  have hfix : Stellmacher.PushingUp.AmalgamGraph.act R g a = a := hg
  have hfixInv : Stellmacher.PushingUp.AmalgamGraph.act R g⁻¹ a = a :=
    (stabilizer R a).inv_mem hg
  have hQ : (Q R a).map (MulAut.conj g).toMonoidHom = Q R a := by
    simpa only [hfixInv, inv_inv] using (Q_act R g⁻¹ a).symm
  have hL : (Ltilde R a).map (MulAut.conj g⁻¹).toMonoidHom = Ltilde R a := by
    simpa only [hfix] using (Ltilde_act R g a).symm
  constructor
  · have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hx.1
    rw [hQ] at hh
    exact hh
  · intro y hy
    have hy' : g⁻¹ * y * g ∈ Ltilde R a := by
      have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hy
      rw [hL] at hh
      simpa only [MulAut.conj_apply, inv_inv, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe] using hh
    have hh := congrArg (fun z => g * z * g⁻¹) (hx.2 _ hy')
    simpa [mul_assoc] using hh

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

private theorem finite_kernel (a : Vertex R) : Finite (Q R a) := by
  let := finite_stabilizer R a
  exact Finite.of_injective (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)

theorem edge_kernel_two (source : LocalSource L R) (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) : IsPGroup 2 (Q R b) := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a b).mp hab
  · have hh := Q_act R g (beta R)
    simp only [beta, act_hVertex, one_mul] at hh
    rw [hh]
    change IsPGroup 2 ((neighborhoodKernel R (hVertex R 1)).map _)
    rw [neighborhoodKernel_h_base_eq_Sbar]
    exact (source.two_group.of_surjective (embedS R).rangeRestrict
      (embedS R).rangeRestrict_surjective).map _
  · change true = false at ha
    cases ha

private theorem proper_commutator {G : Type*} [Group G]
    (P A : Subgroup G) [Finite P] (hp : IsPGroup 2 P)
    (hAP : A ≤ P) (hne : A ≠ ⊥) : ⁅A, P⁆ ≠ A := by
  intro heq
  let A₀ := A.subgroupOf P
  have hcomm : ⁅A₀, (⊤ : Subgroup P)⁆ = A₀ := by
    apply map_injective P.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hAP, ← MonoidHom.range_eq_map, range_subtype, heq]
  have hz : A₀ ≤ ⊥ := le_normal_of_quotient_isPGroup_of_eq_commutator
    A₀ ⊤ ⊥ (hp.to_quotient ⊥) hcomm
  have hh := congrArg (Subgroup.map P.subtype) (le_bot_iff.mp hz)
  rw [map_subgroupOf_eq_of_le hAP, Subgroup.map_bot] at hh
  exact hne hh

variable (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
include hb modules

omit modules in
theorem radius_le_Q (a : Vertex R) (ha : color R a = false) : V R a ≤ Q R a :=
  geometry.V_le_Q hb a ha

omit modules in
theorem Z_le_B (a : Vertex R) (ha : color R a = false) :
    Z R a ≤ B R a (geometry.Z_normal a) := by
  intro x hx
  apply (mem_B_iff R a (geometry.Z_normal a)
    ((radius_le_Q hb a ha).trans (fun _ hv => hv.1)) x).mpr
  refine ⟨Z_le_VBall R a 2 hx, fun l hl => ?_⟩
  exact le_normalizer_iff_commutator_le_right.mp
    ((show Ltilde R a ≤ stabilizer R a from map_subtype_le _).trans (Z_normalized R a))
      (commutator_mem_commutator hl hx)

omit modules in
theorem B_le_radius (a : Vertex R) (ha : color R a = false) :
    B R a (geometry.Z_normal a) ≤ V R a := by
  intro x hx
  exact ((mem_B_iff R a (geometry.Z_normal a)
    ((radius_le_Q hb a ha).trans (fun _ hv => hv.1)) x).mp hx).1

omit [Finite M] modules in
theorem edge_Z_le_Q (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) : Z R a ≤ Q R b := by
  apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
  rw [geometry.distance_constant a ha,
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)]
  exact lt_trans (by decide : 1 < 2) hb

omit [Finite M] in
theorem edge_Z_eq_fixed (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) :
    Z R b = Z R a ⊓ centralizer (Q R b : Set (FreeAmalgam R)) := by
  have hcolor : color R b ≠ false := fun hb => (adjacent_color_ne R hab) (ha.trans hb.symm)
  apply le_antisymm
  · refine le_inf (edge_Z_le a b ha hab) ?_
    rw [Z, if_neg hcolor]
    intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  · rintro x ⟨hx, hxc⟩
    rw [Z, if_neg hcolor]
    apply mem_omegaCenter_iff.mpr
    have hZa : Z R a ≤ Q R b := by
      apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
      rw [geometry.distance_constant a ha,
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)]
      exact lt_trans (by decide : 1 < 2) hb
    have hxω : x ∈ omegaCenter (Q R a) := by
      change x ∈ X R a
      rwa [modules.X_eq_Z a ha]
    exact ⟨hZa hx, (mem_omegaCenter_iff.mp hxω).2.1, hxc⟩

theorem edge_commutator_eq_natural
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ = ⁅U R a, Q R b⁆ := by
  let naturalData : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hQ : Q R b ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hZa := edge_Z_le_Q hb a b ha hab
  have hh := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (naturalData.decomposition_at a ha).symm)
    (inf_le_right.trans (centralizer_le hQ))
    ((U_le_Z a).trans (hZa.trans (Q R b).le_normalizer))
  rw [commutator_comm, ← hh, commutator_comm]

theorem edge_commutator_le_natural
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ ≤ U R a := by
  rw [edge_commutator_eq_natural hb modules a b ha hab]
  exact le_normalizer_iff_commutator_le_left.mp
    ((show Q R b ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hab)).trans
      (U_normalized a))

omit hb in
theorem edge_commutator_ne_bot
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ ≠ ⊥ := by
  intro hbot
  have hcentral : Q R b ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot)
  have heq : Q R b = Q R a := by
    rw [← source.adjacent_centralizer geometry.radical_ne_bot a b ha hab, inf_eq_left.mpr hcentral]
  have hQa : Q R a = ⊥ := by
    apply no_common_normal_at_edge R source.characteristic a b ha hab (Q R a)
    · exact le_inf (fun _ hx => hx.1) (fun _ hx => hx.2 b hab)
    · exact Q_normal R a
    · rw [← heq]
      exact Q_normal R b
  have hU : U R a = ⊥ := by
    apply le_bot_iff.mp
    have hZ : Z R a ≤ Q R a := by
      rw [← modules.X_eq_Z a ha]
      exact omegaCenter_le _
    exact hQa ▸ (U_le_Z a).trans hZ
  have hc := modules.natural.card_at a ha
  rw [hU, Nat.card_eq_fintype_card] at hc
  simp at hc

theorem edge_displacement_card_le_four (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) :
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  let := finite_kernel (R := R) b
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [modules.natural.card_at a ha]; decide)
  have hU := edge_commutator_le_natural hb modules a b ha hab
  let : Finite (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hU) (inclusion_injective hU)
  have hne : ⁅Z R a, Q R b⁆ ≠ U R a := by
    rw [edge_commutator_eq_natural hb modules a b ha hab]
    apply proper_commutator (Q R b) (U R a) (edge_kernel_two source a b ha hab)
      ((U_le_Z a).trans (edge_Z_le_Q hb a b ha hab))
    intro h
    have hh := modules.natural.card_at a ha
    rw [h] at hh
    simp at hh
  have hdvd := card_dvd_of_le hU
  rw [modules.natural.card_at a ha] at hdvd
  have hlt : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) < 8 := by
    by_contra! hh
    apply hne
    exact eq_of_le_of_card_ge hU (by rwa [modules.natural.card_at a ha])
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

omit [Finite M] hb in
theorem U_fixed_eq_bot
    (a : Vertex R) (ha : color R a = false) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
  have hbase : U R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact (disjoint_iff.mp modules.disjoint).le ⟨hx.1, U_le_Z _ hx.1, hx.2⟩
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hu := U_act R g (alpha R)
  have hl := Ltilde_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hu hl
  apply le_bot_iff.mp
  rintro x ⟨hx, hc⟩
  rw [hu] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyc : y ∈ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
    intro l hll
    have hll' : (MulAut.conj g⁻¹) l ∈ Ltilde R (mVertex R g) := by
      rw [hl]
      exact mem_map_of_mem _ hll
    have he := hc _ hll'
    apply (MulAut.conj g⁻¹).injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using he
  have hy1 : y = 1 := hbase.le ⟨hy, hyc⟩
  simp only [hy1, map_one, mem_bot]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
