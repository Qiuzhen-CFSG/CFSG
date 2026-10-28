module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalFFSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalStationarySelection
public import Theory.Representation.SL2NaturalFixedLifting.PointSylow
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.CoprimeFixedDisplacement
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.PCoreImage
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient

/-!
# Comparing the original Cartan module with its omega-span

A natural fixed quotient of the original reduced W has a Sylow-fixed
point outside C_W(L), by fixed-point lifting through the exact central
kernel. On C_W(T ∩ L), the Cartan displacement equals the Borel
displacement, so T normalizes it. If L centralized Ω₁Z(T), coprime
fixed/moved disjointness would force this displacement to vanish. The
nonzero natural point and the odd Cartan action contradict that conclusion.

Thus the omega-span is noncentral in the natural row. Its Sylow
centralizer and that of W are both O₂(LT), so Thompson movement transfers
between these two particular reduced inputs. The symmetric-five row has
degree two already. Together with the stationary constituent argument this
proves the exact small-generation premise of 5.2.2, with no movement,
module-model or omega-centralization hypothesis. Recognition of the
resulting prime pair remains a separate part of the global argument.

Source: Aschbacher--Smith 5.1.2--3 and 5.1.6, printed pp.630--633,
and the first paragraph of 5.2.2, p.647; fixed-point lifting is I.2.3(1),
p.413 (`refs/quasithin.pdf`). The `import all` continues the existing
internal natural point-stabilizer proof without changing its visibility.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

private theorem natural_quotient_sylow_fixed_point
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsNaturalFixedQuotient L W n) (P : Sylow 2 L) :
    ∃ w ∈ W, w ∈ centralizer ((P : Subgroup L).map L.subtype : Set G) ∧
      w ∉ centralizer (L : Set G) := by
  obtain ⟨F,_,_,_,_,e,m,he⟩ := hm
  let := ZMod.algebra F 2
  let := h.reduced.2.1
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let a : L →* MulAut W := W.normalizerMonoidHom.comp (inclusion m.normalizes)
  have hker : q.ker ≤ a.ker := by
    intro l hl
    have hlc : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp (e.map_eq_one_iff.mp hl)
    have hc : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer h.sylow_normalizes)
    have hlW : (l:G) ∈ centralizer (W : Set G) :=
      (h.sylow_centralizer_eq_core.symm ▸ hc (mem_map_of_mem L.subtype hlc)).2
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (l:G)*(w:G)*(l:G)⁻¹=(w:G)
    rw [←hlW w w.property,mul_inv_cancel_right]
  let b : SL(2,F) →* MulAut W := q.liftOfSurjective hq ⟨a,hker⟩
  have hb (l : L) : b (q l) = a l :=
    q.liftOfRightInverse_comp_apply _ _ _ l
  let σ := elementaryRepresentation (p:=2) b
  let f : Additive W →+ (Fin 2 → F) := m.quotient.toAdditiveLeft
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := m.surjective (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w,hw⟩
  have ha (l : L) (w : Additive W) : σ (q l) w = Additive.ofMul (a l w.toMul) := by
    change Additive.ofMul (b (q l) w.toMul) = _
    rw [hb]
  have hfe (g : SL(2,F)) (w : Additive W) : f (σ g w) = g • f w := by
    obtain ⟨l,rfl⟩ := hq g
    rw [ha]
    have hh := m.equivariant l w.toMul
    rw [he] at hh
    exact hh
  have hfk (w : Additive W) (hw : f w = 0) (g : SL(2,F)) : σ g w = w := by
    obtain ⟨l,rfl⟩ := hq g
    rw [ha]
    apply Additive.toMul.injective
    apply Subtype.ext
    have hwc : (w.toMul:G) ∈ centralizer (L : Set G) := by
      have hh : w.toMul ∈ m.quotient.ker := hw
      rwa [m.kernel] at hh
    change (l:G)*(w.toMul:G)*(l:G)⁻¹=(w.toMul:G)
    rw [hwc l l.property,mul_inv_cancel_right]
  obtain ⟨v,hv⟩ := exists_ne (0 : Fin 2 → F)
  obtain ⟨w,hw⟩ := hf v
  let Q := P.mapSurjective hq
  obtain ⟨g,hg⟩ := SL2NaturalFixedLifting.exists_conjugate_fixed_of_fixed_kernel
    σ f hf hfe hfk (Q : Subgroup SL(2,F)) Q.isPGroup' w
  let w' := σ g⁻¹ w
  have hfw : f w' ≠ 0 := by
    intro hz
    have heq : σ g w' = w := by
      change σ g (σ g⁻¹ w) = w
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    have hh := congrArg f heq
    rw [hfe,hz,smul_zero] at hh
    exact hv (hw.symm.trans hh.symm)
  refine ⟨w'.toMul,w'.toMul.property,?_,?_⟩
  · rintro _ ⟨l,hl,rfl⟩
    have hfix := hg (q l) (mem_map_of_mem q hl)
    have hh : σ (q l) w' = w' := by
      have hc := congrArg (σ g⁻¹) hfix
      have hword : g⁻¹ * (MulAut.conj g) (q l) = q l * g⁻¹ := by
        simp only [MulAut.conj_apply,mul_assoc,inv_mul_cancel_left]
      change σ (q l) (σ g⁻¹ w) = σ g⁻¹ w
      rw [←Module.End.mul_apply,←map_mul]
      simpa only [←Module.End.mul_apply,←map_mul,hword] using hc
    rw [ha] at hh
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun x : Additive W => (x.toMul:G)) hh)
  · intro hc
    apply hfw
    change w'.toMul ∈ m.quotient.ker
    rw [m.kernel]
    exact hc

/-- A natural fixed quotient on the original reduced module forces L to
move the original Sylow omega-center, even when the fixed kernel is nontrivial. -/
theorem Input.natural_quotient_not_centralizes_omega
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (hm : IsNaturalFixedQuotient L W n) :
    ¬ L ≤ omegaCentralizer T := by
  intro hLC
  let U := (T : Subgroup G) ⊓ L
  let V := W ⊓ centralizer (U : Set G)
  let := h.reduced.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le inf_le_left
  have hLW : L ≤ normalizer (W : Set G) := le_sup_left.trans (reduced_normalizes h.reduced)
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    le_sup_right.trans (reduced_normalizes h.reduced)
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    (le_inf hTW (hTU.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hBV : localBorel T L ≤ normalizer (V : Set G) :=
    (le_inf (inf_le_left.trans hLW)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hAV : A ≤ normalizer (V : Set G) := c.left_le.trans hBV
  have hTB : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes (hTU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hmove : ⁅V,A⁆ = ⁅V,localBorel T L⁆ :=
    commutator_eq_of_centralizing_sup (c.left_sup_intersection h.sylow_normalizes)
      (le_centralizer_iff.mp (show V ≤ centralizer (U : Set G) from inf_le_right)) hAV
  have hTVA : (T : Subgroup G) ≤ normalizer (⁅V,A⁆ : Subgroup G) := by
    rw [hmove]
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hTV ht),
      mem_normalizer_iff_map_conj_eq.mp (hTB ht)]
  have hodd : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [hk]
    exact hodd.coprime_two_right.pow_right k
  have hfix : V ⊓ centralizer (T : Set G) ≤ centralizer (A : Set G) := by
    intro v hv
    have hz : v ∈ omegaOneCenterAmbient (T : Subgroup G) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨h.reduced_le_sylow hv.1.1,elemPow_eq_one_of_isElementaryAbelian (p:=2) v hv.1.1,hv.2⟩
    exact centralizer_le (c.left_le.trans inf_le_left) (le_centralizer_iff.mp hLC hz)
  have hzero : ⁅V,A⁆ = ⊥ :=
    commutator_eq_bot_of_fixed_centralizer_of_normalizes_displacement V A T
      (IsElementaryAbelian.isPGroup 2 V) T.isPGroup' hAV hcop hfix hTVA
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
  obtain ⟨w,hw,hwu,hwc⟩ := natural_quotient_sylow_fixed_point h hm P
  have hpmap : (P : Subgroup L).map L.subtype = U := by
    rw [hP,subgroupOf_map_subtype]
  have hwV : w ∈ V := ⟨hw,by rwa [hpmap] at hwu⟩
  have hwA := commutator_eq_bot_iff_le_centralizer.mp hzero hwV
  have hAbot : A = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    have ho : Odd (orderOf a) := hodd.of_dvd_nat (by
      rw [←Subgroup.orderOf_mk a ha]
      exact orderOf_dvd_natCard _)
    exact natural_quotient_odd_point_stabilizer hm (c.left_le ha).1 ho hw hwc
      (by rw [hwA a ha,mul_inv_cancel_right])
  have hcard := c.left_card h.linear h.sylow_normalizes
  rw [hAbot,Subgroup.card_bot] at hcard
  have hp : 2^2 ≤ (2:ℕ)^n := Nat.pow_le_pow_right (by decide) (by have := h.exponent; omega)
  omega

/-- Original-module Thompson movement transfers to the omega-span unless
its source classifier has already supplied degree two. The transfer uses
both actual reduced centralizers; it does not identify the two modules. -/
theorem Input.thompson_moves_omega_or_degree_two
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    (¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∨ n = 2 := by
  rcases h.natural_quotient_or_five_of_thompson_moves hj with hm | ⟨hn,_⟩
  · left
    intro hJU
    let hu := h.omega_span_input (h.natural_quotient_not_centralizes_omega c hm)
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ he => he.1
    have hJcore : elementaryAbelianMaxJ (T : Subgroup G) ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      rw [←hu.sylow_centralizer_eq_core]
      exact le_inf hJT hJU
    apply hj
    intro x hx
    have hh : x ∈ (T : Subgroup G) ⊓ centralizer (W : Set G) :=
      h.sylow_centralizer_eq_core.symm ▸ hJcore hx
    exact hh.2
  · exact Or.inr hn

/-- The complete small-Cartan generation premise used in original 5.2.2.
The original reduced module and its omega-span are compared explicitly,
covering the mixed action case as well as both previous source branches. -/
theorem sourceCartanSmallGeneration :
    SourceCartanSmallGeneration KnownSimple.IsKnownSimple G := by
  intro T L W n h H hH hgen A B c hcontrol hz
  have hescape : ¬ A ≤ normalizer (residual H : Set G) := by
    intro hn
    exact (h.cartan_core_ne_bot_iff hH hcontrol le_rfl).mpr hn hz
  by_cases hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)
  · exact (h.cartanSmallGeneration_of_thompson_centralizes hH c hcontrol hescape hj).2
  · rcases h.thompson_moves_omega_or_degree_two c hj with hu | hn
    · exact (h.cartan_thompson_moving_omega_alternatives hH hgen c hz hu).2.1
    · exact h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inl hn)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
