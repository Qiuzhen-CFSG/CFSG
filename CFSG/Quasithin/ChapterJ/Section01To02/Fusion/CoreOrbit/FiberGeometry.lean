module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Seed
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.FiberGeometry.Rows
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Duality
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.Frattini.PGroup

/-!
# The sixteen-element fiber and its actual Q-conjugators

Fix any seed w in Uα ∩ Q minus HC. The transvection row on U has image Z,
so D = C_U(w) has order sixteen. J.2.4(3) gives C_HC(w) = D; restricting
the class-two commutator row to HC then gives [w,HC] = V. Correcting that
row by a U-element proves [w,h] ∈ Z iff h ∈ U. Since J.2.6(4) puts all
squares of HC in Z, w cannot invert a member of HC minus U. Thus the
involutions of the literal Q/HC fiber are exactly wD.

For v in D minus V, HC⟨w⟩ has order 256 and lies in C_S(v); J.2.3(6)
makes this an equality. J.2.2(5) identifies the same product with HC Dα.
Choose y in Q moving Zα. J.2.3(9) puts w^y outside Uα, hence in the
second V-coset of wD. The commutator row on HC realizes every V-displacement;
composing its actual conjugators with y gives every member of wD.
All conjugation formulas use q*w*q⁻¹, and `coreMap_eq_iff` fixes the coset
convention. Normality is only relative to the groups where it is proved.

`fiberGeometry_of_earlier_source` completes the conditional constructor.
It assumes SourceJ24 (producer `qt-j12-fusion-commutators`), SourceJ26
(producer `qt-j12-fusion-outer`), and precisely J.2.3(6,9) (producer
`qt-j12-special-core`). The transvection, order and containment facts are
proved component APIs of `qt-j12-parabolic-structure`. The optional identity
with Dα takes exactly the actual H/Q image-order clause of J.2.2(5).
Final J.2.8 assembly and discharge of these source inputs remain with
`qt-j12-fusion-core-orbit`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.8, printed pp.437–438 / PDF pp.448–449 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]
open ConjugateIntersections GeometryRows

private theorem seed_mem_S (d : LocalSetup G) (s : ConjugateSeed d.toTypeRuSetup) :
    (s.w : G) ∈ d.toTypeRuSetup.S :=
  conjugateU_le_S d s.ell s.ell.property s.mem_conjugate

private theorem HC_le_S (d : LocalSetup G) : d.toTypeRuSetup.HC ≤ d.toTypeRuSetup.S := by
  have hh := (inf_le_right : d.toTypeRuSetup.HC ≤
    centralizer (d.toTypeRuSetup.U : Set G)).trans
      (centralizer_le (le_conjugateSpan d.toTypeRuSetup.H d.V))
  rwa [d.ru1.centralizer_V] at hh

/-- The nontrivial transvection induced by w has image exactly Z (J.2.2(4)). -/
theorem seed_commutator_U (d : LocalSetup G) (s : ConjugateSeed d.toTypeRuSetup) :
    ⁅zpowers (s.w : G), d.toTypeRuSetup.U⁆ = d.toTypeRuSetup.Z := by
  have hle : ⁅zpowers (s.w : G), d.toTypeRuSetup.U⁆ ≤ d.toTypeRuSetup.Z :=
    (commutator_mono (zpowers_le.mpr s.w.property) le_rfl).trans
      d.toTypeRuSetup.commutator_Q_U_le_Z
  have hn : ⁅zpowers (s.w : G), d.toTypeRuSetup.U⁆ ≠ ⊥ := by
    intro he
    exact s.outside ⟨pCoreIn_le 2 _ s.w.property,
      commutator_eq_bot_iff_le_centralizer.mp he (mem_zpowers _)⟩
  have hh := (one_lt_card_iff_ne_bot _).mpr hn
  apply eq_of_le_of_card_ge hle
  rw [d.card_Z]
  omega

/-- The kernel of the transvection on E32 has order sixteen. -/
theorem seed_centralizer_card (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) :
    Nat.card (seedCentralizer d.toTypeRuSetup s) = 16 := by
  have hh := row_card d ⟨s.w, seed_mem_S d s⟩ _ d.U_le_S
  rw [seed_commutator_U d s, d.card_Z, d.ru2.card_U d.card_Z] at hh
  change 2 * Nat.card (seedCentralizer d.toTypeRuSetup s) = 32 at hh
  omega

private theorem seed_centralizer_HC (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup) :
    d.toTypeRuSetup.HC ⊓ centralizer ({(s.w : G)} : Set G) =
      seedCentralizer d.toTypeRuSetup s := by
  apply le_antisymm
  · intro h hh
    refine ⟨?_, hh.2⟩
    by_contra hn
    have hw : (s.w : G) ∈ d.toTypeRuSetup.Q ⊓ centralizer ({h} : Set G) :=
      ⟨s.w.property, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hh.2).symm⟩
    rw [(h24 h hh.1 hn).2.2] at hw
    exact s.outside ((sup_le (zpowers_le.mpr hh.1) d.U_le_HC) hw)
  · exact inf_le_inf_right _ d.U_le_HC

/-- J.2.4(3) and class-two row counting give the full image V. -/
theorem seed_commutator_HC (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup) :
    ⁅zpowers (s.w : G), d.toTypeRuSetup.HC⁆ = d.V := by
  have hh := row_card d ⟨s.w, seed_mem_S d s⟩ _ (HC_le_S d)
  rw [seed_centralizer_HC d s h24, seed_centralizer_card d s, d.card_HC] at hh
  change Nat.card (⁅zpowers (s.w : G), d.toTypeRuSetup.HC⁆ : Subgroup G) * 16 = 128 at hh
  have hc : Nat.card (⁅zpowers (s.w : G), d.toTypeRuSetup.HC⁆ : Subgroup G) = 8 := by
    omega
  apply eq_of_le_of_card_ge
    ((commutator_mono le_rfl (HC_le_S d)).trans
      (d.ru1.commutator_le_V ⟨s.w, seed_mem_S d s⟩))
  rw [hc, d.ru1.card_V]

private theorem HC_square_mem_Z (d : LocalSetup G) {z : G}
    (h26 : SourceJ26 d.toTypeRuSetup z) (h : d.toTypeRuSetup.HC) :
    (h : G)^2 ∈ d.toTypeRuSetup.Z := by
  let : Fact (IsPGroup 2 d.toTypeRuSetup.HC) :=
    ⟨(isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
      (inclusion d.toTypeRuSetup.HC_le_Q) (inclusion_injective _)⟩
  rw [← h26.2.2.2.2.1]
  exact mem_map.mpr ⟨h^2, pth_power_mem_frattini_of_isPGroup (p := 2) h, rfl⟩

/-- The centralizer of w modulo the actual Z, restricted to HC, is exactly U. -/
theorem seed_commutator_mem_Z_iff (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup)
    (h : d.toTypeRuSetup.HC) :
    ⁅(s.w : G), (h : G)⁆ ∈ d.toTypeRuSetup.Z ↔ (h : G) ∈ d.toTypeRuSetup.U := by
  constructor
  · intro hz
    have hr : ⁅(s.w : G), (h : G)⁆ ∈
        (row d ⟨s.w, seed_mem_S d s⟩ _ d.U_le_S).range := by
      rw [row_range, seed_commutator_U d s]
      exact hz
    obtain ⟨u, hu⟩ := hr
    let f := row d ⟨s.w, seed_mem_S d s⟩ _ (HC_le_S d)
    have he : f (h * (inclusion d.U_le_HC u)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      change ⁅(s.w : G), (h : G)⁆ * ⁅(s.w : G), (u : G)⁆⁻¹ = 1
      change ⁅(s.w : G), (u : G)⁆ = ⁅(s.w : G), (h : G)⁆ at hu
      rw [hu, mul_inv_cancel]
    have hc : (h : G) * (u : G)⁻¹ ∈ seedCentralizer d.toTypeRuSetup s := by
      rw [← seed_centralizer_HC d s h24]
      exact ⟨d.toTypeRuSetup.HC.mul_mem h.property
          (d.toTypeRuSetup.HC.inv_mem (d.U_le_HC u.property)),
        mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp he).symm⟩
    simpa only [inv_mul_cancel_right] using d.toTypeRuSetup.U.mul_mem hc.1 u.property
  · intro hu
    exact d.toTypeRuSetup.commutator_Q_U_le_Z
      (commutator_mem_commutator s.w.property hu)

/-- No member of HC minus U is inverted by w; its square lies in Φ(HC) = Z. -/
theorem seed_not_invert (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup)
    {z : G} (h26 : SourceJ26 d.toTypeRuSetup z)
    (h : d.toTypeRuSetup.HC) (hu : (h : G) ∉ d.toTypeRuSetup.U) :
    (s.w : G) * h * (s.w : G)⁻¹ ≠ (h : G)⁻¹ := by
  intro he
  apply hu
  apply (seed_commutator_mem_Z_iff d s h24 h).mp
  rw [commutatorElement_def, he, ← mul_inv_rev, ← pow_two]
  exact d.toTypeRuSetup.Z.inv_mem (HC_square_mem_Z d h26 h)

/-- The involutions in the literal quotient fiber are precisely w C_U(w). -/
theorem seed_fiber_iff (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup)
    {z : G} (h26 : SourceJ26 d.toTypeRuSetup z) (x : d.toTypeRuSetup.Q) :
    x ∈ fiber d.toTypeRuSetup (coreMap d.toTypeRuSetup s.w) ↔
      (s.w : G)⁻¹ * x ∈ seedCentralizer d.toTypeRuSetup s := by
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  have hw2 : (s.w : G)^2 = 1 := by
    rw [← s.order_two d.toTypeRuSetup d.card_Z]
    exact pow_orderOf_eq_one _
  have hwi : (s.w : G)⁻¹ = s.w := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hw2)
  constructor
  · rintro ⟨hx, hx2⟩
    have hh := (coreMap_eq_iff d.toTypeRuSetup x s.w).mp hx
    let h : d.toTypeRuSetup.HC := ⟨(s.w : G)⁻¹ * x, hh⟩
    have hxi : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_left (by
      simpa only [← pow_two, ← hx2] using pow_orderOf_eq_one (x : G))
    have hi : (s.w : G) * h * (s.w : G)⁻¹ = (h : G)⁻¹ := by
      change (s.w : G) * ((s.w : G)⁻¹ * x) * (s.w : G)⁻¹ =
        ((s.w : G)⁻¹ * x)⁻¹
      calc
        _ = (x : G) * (s.w : G)⁻¹ := by group
        _ = _ := by simp only [mul_inv_rev, hxi, hwi]
    have hu : (h : G) ∈ d.toTypeRuSetup.U := by
      by_contra hn
      exact seed_not_invert d s h24 h26 h hn hi
    refine ⟨hu, mem_centralizer_singleton_iff.mpr ?_⟩
    have hhi : (h : G)⁻¹ = h := inv_eq_of_mul_eq_one_left (by
      simpa only [← pow_two] using elemPow_eq_one_of_isElementaryAbelian (h : G) hu)
    rw [hhi] at hi
    exact (mul_inv_eq_iff_eq_mul.mp hi).symm
  · intro hh
    have hhC := d.U_le_HC hh.1
    refine ⟨(coreMap_eq_iff d.toTypeRuSetup x s.w).mpr hhC, ?_⟩
    let h : G := (s.w : G)⁻¹ * x
    have hc : Commute (s.w : G) h :=
      (mem_centralizer_singleton_iff.mp hh.2).symm
    have hx : (x : G) = (s.w : G) * h := by simp [h]
    apply orderOf_eq_prime
    · rw [hx, hc.mul_pow, hw2,
        elemPow_eq_one_of_isElementaryAbelian h hh.1, one_mul]
    · intro he
      have hi : (s.w : G)⁻¹ ∈ d.toTypeRuSetup.HC := by simpa [he] using hhC
      exact s.outside (by simpa only [inv_inv] using d.toTypeRuSetup.HC.inv_mem hi)

private theorem V_le_seedCentralizer (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) : d.V ≤ seedCentralizer d.toTypeRuSetup s := by
  intro v hv
  exact ⟨le_conjugateSpan _ _ hv, mem_centralizer_singleton_iff.mpr
    (d.ru1.central_V hv s.w (seed_mem_S d s)).symm⟩

private theorem seed_join_card (d : LocalSetup G) (s : ConjugateSeed d.toTypeRuSetup) :
    Nat.card (d.toTypeRuSetup.HC ⊔ zpowers (s.w : G) : Subgroup G) = 256 := by
  classical
  have hd : Disjoint d.toTypeRuSetup.HC (zpowers (s.w : G)) := by
    apply disjoint_def.mpr
    intro x hx hxw
    have he : x = 1 ∨ x = (s.w : G) := by
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp
        (mem_zpowers_iff_mem_range_orderOf.mp hxw)
      have hn2 : n < 2 := by
        simpa only [s.order_two d.toTypeRuSetup d.card_Z] using Finset.mem_range.mp hn
      interval_cases n <;> simp
    exact he.resolve_right (fun he => s.outside (he ▸ hx))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    ((zpowers_le.mpr (pCoreIn_le 2 _ s.w.property)).trans
      (centralizer_normalized d.toTypeRuSetup)) hd,
    d.card_HC, Nat.card_zpowers, s.order_two d.toTypeRuSetup d.card_Z]

private theorem seed_centralizer_eq_join (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup)
    (h236 : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V)
    {v : G} (hv : v ∈ seedCentralizer d.toTypeRuSetup s) (hvV : v ∉ d.V) :
    d.toTypeRuSetup.S ⊓ centralizer ({v} : Set G) =
      d.toTypeRuSetup.HC ⊔ zpowers (s.w : G) := by
  have hle : d.toTypeRuSetup.HC ⊔ zpowers (s.w : G) ≤
      d.toTypeRuSetup.S ⊓ centralizer ({v} : Set G) := by
    apply sup_le
    · exact le_inf (HC_le_S d) (fun h hh =>
        mem_centralizer_singleton_iff.mpr (hh.2 v hv.1).symm)
    · exact zpowers_le.mpr ⟨seed_mem_S d s,
        mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hv.2).symm⟩
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [seed_join_card d s, d.ru1.centralizer_card_of_full_commutator
    ⟨v, d.U_le_S hv.1⟩ (h236 ⟨v, d.U_le_S hv.1⟩ hvV)]

/-- J.2.3(6) produces v in D minus V whose entire S-centralizer lies in Q. -/
theorem seed_centralizer_control (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup)
    (h236 : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V) :
    ∃ v ∈ seedCentralizer d.toTypeRuSetup s, v ∉ d.V ∧
      d.toTypeRuSetup.S ⊓ centralizer ({v} : Set G) ≤ d.toTypeRuSetup.Q := by
  have hn : ¬ seedCentralizer d.toTypeRuSetup s ≤ d.V := by
    intro hl
    have hc := card_le_of_le hl
    rw [seed_centralizer_card d s, d.ru1.card_V] at hc
    omega
  obtain ⟨v, hv, hvV⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨v, hv, hvV, ?_⟩
  rw [seed_centralizer_eq_join d s h236 hv hvV]
  exact sup_le d.toTypeRuSetup.HC_le_Q (zpowers_le.mpr s.w.property)

private theorem seed_conjugate_ne (d : LocalSetup G) (s : ConjugateSeed d.toTypeRuSetup) :
    conjugateU d s.ell ≠ d.toTypeRuSetup.U := by
  intro he
  exact s.outside (d.U_le_HC (he ▸ s.mem_conjugate))

private theorem exists_moves_conjugateZ (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) :
    ∃ y : d.toTypeRuSetup.Q, (y : G) ∉ centralizer (conjugateZ d s.ell : Set G) := by
  have hn : conjugateZ d s.ell ≠ d.toTypeRuSetup.Z := by
    intro he
    have hl : (s.ell : G) ∈ normalizer (d.toTypeRuSetup.Z : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr he
    exact seed_conjugate_ne d s (conjugateU_eq_of_mem_H d s.ell
      (normalizer_le_centralizer_of_card_two _ d.card_Z hl))
  have hnQ : ¬ d.toTypeRuSetup.Q ≤ centralizer (conjugateZ d s.ell : Set G) := by
    intro hc
    have hle : conjugateZ d s.ell ≤ d.toTypeRuSetup.Z := by
      rw [← d.centralizer_Q_inf_U]
      exact le_inf ((conjugateZ_le_V d s.ell s.ell.property).trans
        (le_conjugateSpan _ _)) (le_centralizer_iff.mp hc)
    apply hn
    apply eq_of_le_of_card_ge hle
    rw [card_map_of_injective (MulAut.conj (s.ell : G)).injective]
  obtain ⟨y, hy, hyn⟩ := SetLike.not_le_iff_exists.mp hnQ
  exact ⟨⟨y, hy⟩, hyn⟩

private theorem conjugated_mover_not_mem_H (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (y : d.toTypeRuSetup.Q)
    (hy : (y : G) ∉ centralizer (conjugateZ d s.ell : Set G)) :
    (s.ell : G)⁻¹ * y * s.ell ∉ d.toTypeRuSetup.H := by
  intro hk
  apply hy
  rintro a ⟨z, hz, rfl⟩
  change (s.ell : G) * z * (s.ell : G)⁻¹ * y =
    (y : G) * ((s.ell : G) * z * (s.ell : G)⁻¹)
  calc
    _ = (s.ell : G) * (z * ((s.ell : G)⁻¹ * y * s.ell)) * (s.ell : G)⁻¹ := by group
    _ = (s.ell : G) * (((s.ell : G)⁻¹ * y * s.ell) * z) * (s.ell : G)⁻¹ := by
      rw [hk z hz]
    _ = _ := by group

private theorem moved_seed_not_mem_conjugate (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup)
    (h239 : ∀ l : d.L, (l : G) ∉ d.toTypeRuSetup.H →
      d.toTypeRuSetup.U ⊓ conjugateU d l = d.V)
    (y : d.toTypeRuSetup.Q)
    (hy : (y : G) ∉ centralizer (conjugateZ d s.ell : Set G)) :
    (y : G) * s.w * (y : G)⁻¹ ∉ conjugateU d s.ell := by
  intro hx
  let k : d.L := ⟨(s.ell : G)⁻¹ * y * s.ell,
    d.L.mul_mem (d.L.mul_mem (d.L.inv_mem s.ell.property) (d.Q_le_L y.property))
      s.ell.property⟩
  have hk := h239 k (conjugated_mover_not_mem_H d s y hy)
  obtain ⟨u, hu, he⟩ := s.mem_conjugate
  obtain ⟨v, hv, hvx⟩ := hx
  change (s.ell : G) * u * (s.ell : G)⁻¹ = s.w at he
  change (s.ell : G) * v * (s.ell : G)⁻¹ = (y : G) * s.w * (y : G)⁻¹ at hvx
  have hconj : (MulAut.conj (k : G)) u = v := by
    apply (MulAut.conj (s.ell : G)).injective
    change (s.ell : G) * ((k : G) * u * (k : G)⁻¹) * (s.ell : G)⁻¹ =
      (s.ell : G) * v * (s.ell : G)⁻¹
    calc
      _ = (y : G) * ((s.ell : G) * u * (s.ell : G)⁻¹) * (y : G)⁻¹ := by
        dsimp [k]
        group
      _ = (y : G) * s.w * (y : G)⁻¹ := by rw [he]
      _ = _ := hvx.symm
  have hvV : v ∈ d.V := by
    rw [← hk]
    exact ⟨hv, mem_map.mpr ⟨u, hu, hconj⟩⟩
  have hxV : (y : G) * s.w * (y : G)⁻¹ ∈ d.V := by
    rw [← hvx]
    exact (mem_normalizer_iff.mp (d.ru1.normalizer_eq ▸ s.ell.property) v).mp hvV
  have hny : (y : G) ∈ normalizer (d.V : Set G) :=
    d.ru1.normalizer_eq ▸ d.Q_le_L y.property
  have hwV : (s.w : G) ∈ d.V :=
    (mem_normalizer_iff.mp hny (s.w : G)).mpr hxV
  exact s.outside (V_le_HC d hwV)

private theorem Q_conjugate_mem_seed_fiber (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (y : d.toTypeRuSetup.Q) :
    y * s.w * y⁻¹ ∈ fiber d.toTypeRuSetup (coreMap d.toTypeRuSetup s.w) := by
  refine ⟨(coreMap_eq_iff d.toTypeRuSetup _ _).mpr ?_, ?_⟩
  · apply (d.dualSection.coordinates_eq_one_iff (s.w⁻¹ * (y * s.w * y⁻¹))).mp
    simp only [map_mul, map_inv]
    rw [mul_comm (d.dualSection.coordinates y) (d.dualSection.coordinates s.w),
      mul_inv_cancel_right, inv_mul_cancel]
  · change orderOf ((MulAut.conj (y : G)) (s.w : G)) = 2
    rw [(MulAut.conj (y : G)).orderOf_eq, s.order_two d.toTypeRuSetup d.card_Z]

private theorem seed_HC_conjugator (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup)
    (v : G) (hv : v ∈ d.V) :
    ∃ h : d.toTypeRuSetup.HC, (h : G) * s.w * (h : G)⁻¹ = (s.w : G) * v := by
  have hvR : v ∈ (row d ⟨s.w, seed_mem_S d s⟩ _ (HC_le_S d)).range := by
    rw [row_range, seed_commutator_HC d s h24]
    exact hv
  obtain ⟨h, hh⟩ := hvR
  refine ⟨h, ?_⟩
  have hc := d.ru1.central_V hv s.w (seed_mem_S d s)
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by
    simpa only [← pow_two] using
      elemPow_eq_one_of_isElementaryAbelian v (le_conjugateSpan d.toTypeRuSetup.H d.V hv))
  calc
    _ = ⁅(s.w : G), (h : G)⁆⁻¹ * s.w := by rw [commutatorElement_def]; group
    _ = v⁻¹ * s.w := by rw [← row_apply d ⟨s.w, seed_mem_S d s⟩ _ (HC_le_S d), hh]
    _ = (s.w : G) * v := by rw [hvi]; exact hc.symm

private theorem seed_second_coset (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup)
    {z : G} (h26 : SourceJ26 d.toTypeRuSetup z)
    (h239 : ∀ l : d.L, (l : G) ∉ d.toTypeRuSetup.H →
      d.toTypeRuSetup.U ⊓ conjugateU d l = d.V) :
    ∃ y : d.toTypeRuSetup.Q, ∃ a ∈ seedCentralizer d.toTypeRuSetup s,
      a ∉ d.V ∧ (y : G) * s.w * (y : G)⁻¹ = (s.w : G) * a := by
  obtain ⟨y, hy⟩ := exists_moves_conjugateZ d s
  have ha := (seed_fiber_iff d s h24 h26 (y * s.w * y⁻¹)).mp
    (Q_conjugate_mem_seed_fiber d s y)
  refine ⟨y, (s.w : G)⁻¹ * ((y : G) * s.w * (y : G)⁻¹), ha, ?_, ?_⟩
  · intro hv
    apply moved_seed_not_mem_conjugate d s h239 y hy
    have hp := (conjugateU d s.ell).mul_mem s.mem_conjugate
      (V_le_conjugateU d s.ell s.ell.property hv)
    simpa only [mul_inv_cancel_left] using hp
  · group

private theorem seed_same_nontrivial_V_coset (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup)
    {a b : G} (ha : a ∈ seedCentralizer d.toTypeRuSetup s)
    (hb : b ∈ seedCentralizer d.toTypeRuSetup s) (haV : a ∉ d.V) (hbV : b ∉ d.V) :
    a⁻¹ * b ∈ d.V := by
  let N := d.V.subgroupOf (seedCentralizer d.toTypeRuSetup s)
  have hc : Nat.card N = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (V_le_seedCentralizer d s)).toEquiv,
      d.ru1.card_V]
  have hi : N.index = 2 := by
    have hh := N.index_mul_card
    rw [hc, seed_centralizer_card d s] at hh
    omega
  have haN : (⟨a, ha⟩ : seedCentralizer d.toTypeRuSetup s)⁻¹ ∉ N := by
    change a⁻¹ ∉ d.V
    simpa only [inv_mem_iff] using haV
  have hbN : (⟨b, hb⟩ : seedCentralizer d.toTypeRuSetup s) ∉ N := hbV
  exact (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false haN hbN)

/-- Every involution in the fiber is conjugate to w by an actual element of Q. -/
theorem seed_Q_conjugator (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup)
    {z : G} (h26 : SourceJ26 d.toTypeRuSetup z)
    (h239 : ∀ l : d.L, (l : G) ∉ d.toTypeRuSetup.H →
      d.toTypeRuSetup.U ⊓ conjugateU d l = d.V)
    (x : fiber d.toTypeRuSetup (coreMap d.toTypeRuSetup s.w)) :
    ∃ q : d.toTypeRuSetup.Q, (q : G) * s.w * (q : G)⁻¹ = x := by
  let b : G := (s.w : G)⁻¹ * x
  have hb : b ∈ seedCentralizer d.toTypeRuSetup s :=
    (seed_fiber_iff d s h24 h26 x).mp x.property
  have hwb : (s.w : G) * b = x := by simp [b]
  by_cases hbV : b ∈ d.V
  · obtain ⟨h, hh⟩ := seed_HC_conjugator d s h24 b hbV
    exact ⟨⟨h, d.toTypeRuSetup.HC_le_Q h.property⟩, hh.trans hwb⟩
  · obtain ⟨y, a, ha, haV, hya⟩ := seed_second_coset d s h24 h26 h239
    have hab := seed_same_nontrivial_V_coset d s ha hb haV hbV
    obtain ⟨h, hh⟩ := seed_HC_conjugator d s h24 (a⁻¹ * b) hab
    let q : d.toTypeRuSetup.Q := ⟨(h : G) * y,
      d.toTypeRuSetup.Q.mul_mem (d.toTypeRuSetup.HC_le_Q h.property) y.property⟩
    refine ⟨q, ?_⟩
    have hac : (h : G) * a * (h : G)⁻¹ = a := by
      rw [← h.property.2 a ha.1, mul_inv_cancel_right]
    have habc : a * b = b * a := by
      let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
      exact congrArg Subtype.val (mul_comm (⟨a, ha.1⟩ : d.toTypeRuSetup.U) ⟨b, hb.1⟩)
    calc
      _ = (h : G) * ((y : G) * s.w * (y : G)⁻¹) * (h : G)⁻¹ := by dsimp [q]; group
      _ = ((h : G) * s.w * (h : G)⁻¹) * ((h : G) * a * (h : G)⁻¹) := by
        rw [hya]
        group
      _ = (s.w : G) * (a⁻¹ * b) * a := by rw [hh, hac]
      _ = (s.w : G) * b := by rw [mul_assoc, mul_assoc, ← habc, inv_mul_cancel_left]
      _ = x := hwb

/-- J.2.2(5), through the actual H/Q image, gives Dα = V⟨w⟩. -/
theorem seed_conjugate_intersection_eq (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup)
    (himage : Nat.card (((conjugateU d s.ell).subgroupOf d.toTypeRuSetup.H).map
      d.ru2.quotientMap) = 2) :
    conjugateU d s.ell ⊓ d.toTypeRuSetup.Q = d.V ⊔ zpowers (s.w : G) := by
  let A := conjugateU d s.ell ⊓ d.toTypeRuSetup.Q
  have hVA : d.V ≤ A := le_inf (V_le_conjugateU d s.ell s.ell.property)
    ((V_le_HC d).trans d.toTypeRuSetup.HC_le_Q)
  have hwA : (s.w : G) ∈ A := ⟨s.mem_conjugate, s.w.property⟩
  have hcard : Nat.card A = 16 := card_conjugate_intersection_Q d.toTypeRuSetup _
    (conjugateU_le_H d s.ell s.ell.property) (card_conjugateU d s.ell) himage
  let N := d.V.subgroupOf A
  have hc : Nat.card N = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVA).toEquiv, d.ru1.card_V]
  have hi : N.index = 2 := by
    have hh := N.index_mul_card
    rw [hc, hcard] at hh
    omega
  have hwN : (⟨s.w, hwA⟩ : A)⁻¹ ∉ N := by
    change (s.w : G)⁻¹ ∉ d.V
    rw [inv_mem_iff]
    exact fun hw => s.outside (V_le_HC d hw)
  apply le_antisymm
  · intro a ha
    by_cases haV : a ∈ d.V
    · exact (le_sup_left : d.V ≤ d.V ⊔ zpowers (s.w : G)) haV
    · have hm : (s.w : G)⁻¹ * a ∈ d.V :=
        (N.mul_mem_iff_of_index_two hi).mpr
          (show (⟨s.w, hwA⟩ : A)⁻¹ ∈ N ↔ (⟨a, ha⟩ : A) ∈ N from
            iff_of_false hwN haV)
      have hp := (d.V ⊔ zpowers (s.w : G)).mul_mem
        ((le_sup_right : zpowers (s.w : G) ≤ d.V ⊔ zpowers (s.w : G)) (mem_zpowers _))
        ((le_sup_left : d.V ≤ d.V ⊔ zpowers (s.w : G)) hm)
      simpa only [mul_inv_cancel_left] using hp
  · exact sup_le hVA (zpowers_le.mpr hwA)

/-- The source identity C_S(v) = HC Dα. The join is a subgroup product since
Dα ≤ Q ≤ H and H normalizes HC. -/
theorem seed_centralizer_eq_conjugate_product (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup)
    (himage : Nat.card (((conjugateU d s.ell).subgroupOf d.toTypeRuSetup.H).map
      d.ru2.quotientMap) = 2)
    (h236 : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V)
    {v : G} (hv : v ∈ seedCentralizer d.toTypeRuSetup s) (hvV : v ∉ d.V) :
    d.toTypeRuSetup.S ⊓ centralizer ({v} : Set G) =
      d.toTypeRuSetup.HC ⊔ (conjugateU d s.ell ⊓ d.toTypeRuSetup.Q) := by
  rw [seed_centralizer_eq_join d s h236 hv hvV,
    seed_conjugate_intersection_eq d s himage, ← sup_assoc,
    sup_eq_left.mpr (V_le_HC d)]

/-- Construct all four fiber-geometry fields from genuine earlier source clauses.
The additional explicit premises are exactly the commutator assertion of J.2.3(6)
and the conjugate-intersection assertion J.2.3(9). Their producer is
`qt-j12-special-core`; SourceJ24 and SourceJ26 retain their own source producers.
No field of FiberGeometry or later J.2.8 conclusion is assumed. -/
theorem fiberGeometry_of_earlier_source (d : LocalSetup G)
    (s : ConjugateSeed d.toTypeRuSetup) (h24 : SourceJ24 d.toTypeRuSetup)
    {z : G} (h26 : SourceJ26 d.toTypeRuSetup z)
    (h236 : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V)
    (h239 : ∀ l : d.L, (l : G) ∉ d.toTypeRuSetup.H →
      d.toTypeRuSetup.U ⊓ conjugateU d l = d.V) :
    FiberGeometry d.toTypeRuSetup s where
  involutions := seed_fiber_iff d s h24 h26
  centralizer_card := seed_centralizer_card d s
  conjugate := seed_Q_conjugator d s h24 h26 h239
  centralizer_control := seed_centralizer_control d s h236

end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
