module
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Involutions fixed modulo a central direct factor

In a finite two-group P, let the normal subgroup R split as V times C,
where V is central and intersects C trivially. A central involution of
R/V lifts uniquely to an involution of C centralizing R. Its commutators
with the whole P lie in V. The factor C need not be P-invariant.

For the relative normalizer N_P(R), centrality of an irreducible factor V
can itself be derived from exact involution-centralizer kernels. The
nontrivial subgroup C_R(N_P(R)) either moves onto V under the irreducible
actor or contains a forbidden involution centralized by N_P(R).

The source consumer is the final pushing-up contradiction in
Aschbacher--Smith 4.2.13, printed p.612. The full central covering factor
must still be identified by that consumer; these statements do not assume
that the covering center is trivial.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A direct central factor supplies an involution fixed modulo the central layer
by the whole two-group. The complement itself need not be invariant. -/
theorem exists_complement_involution_central_modulo
    (hp : IsPGroup 2 G) (R V C : Subgroup G) [R.Normal]
    (hV : V ≤ center G) (hprod : R = V ⊔ C)
    (hdis : V ⊓ C = ⊥) (hne : C ≠ ⊥) :
    ∃ r : G, r ∈ C ∧ orderOf r = 2 ∧
      R ≤ centralizer ({r} : Set G) ∧ ⁅zpowers r,(⊤ : Subgroup G)⁆ ≤ V := by
  let : V.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hV hn) g,mul_inv_cancel_right]
    exact hn⟩
  let q := QuotientGroup.mk' V
  have hqi : Function.Injective (q.comp C.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro c hc
    apply Subtype.ext
    exact hdis.le ⟨(QuotientGroup.eq_one_iff _).mp hc,c.property⟩
  have hRne : R.map q ≠ ⊥ := by
    intro he
    apply hne
    apply le_bot_iff.mp
    intro c hc
    have hcq : q c = 1 := he.le (mem_map_of_mem q (hprod.symm ▸ mem_sup_right hc))
    exact hdis.le ⟨(QuotientGroup.eq_one_iff _).mp hcq,hc⟩
  let : (R.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let Z := center (G ⧸ V) ⊓ R.map q
  have hZne : Z ≠ ⊥ := center_inf_ne_bot_of_normal (hp.to_quotient V) (R.map q) hRne
  have hZtwo : IsPGroup 2 Z := (hp.to_quotient V).to_subgroup Z
  have hd : 2 ∣ Nat.card Z := hZtwo.card_eq_or_dvd.resolve_left
    (fun he => hZne (Subgroup.card_eq_one.mp he))
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 hd
  obtain ⟨a,ha,haz⟩ := z.property.2
  have ha' : a ∈ (V : Set G) * (C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right V C
      ((hV.trans (center_le_centralizer _)).trans (centralizer_le_normalizer _))]
    exact hprod ▸ ha
  obtain ⟨v,hv,c,hc,rfl⟩ := ha'
  have hcz : q c = (z : G ⧸ V) := by
    have hvq : q v = 1 := (QuotientGroup.eq_one_iff _).mpr hv
    simpa only [map_mul,hvq,one_mul] using haz
  have ho : orderOf c = 2 := by
    calc
      orderOf c = orderOf (⟨c,hc⟩ : C) := orderOf_coe (⟨c,hc⟩ : C)
      _ = orderOf (q c) := (orderOf_injective (q.comp C.subtype) hqi ⟨c,hc⟩).symm
      _ = orderOf (z : G ⧸ V) := congrArg orderOf hcz
      _ = 2 := (orderOf_coe z).trans hz
  have hcent : q c ∈ center (G ⧸ V) := hcz.symm ▸ z.property.1
  have hcomm : ⁅zpowers c,(⊤ : Subgroup G)⁆ ≤ V := by
    have hm : (⁅zpowers c,(⊤ : Subgroup G)⁆).map q = ⊥ := by
      rw [map_commutator,MonoidHom.map_zpowers]
      exact commutator_eq_bot_iff_le_centralizer.mpr
        ((zpowers_le.mpr hcent).trans (center_le_centralizer _))
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm
  have hCC : C ≤ centralizer ({c} : Set G) := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    apply congrArg Subtype.val (hqi (a₁ := (⟨s*c, C.mul_mem hs hc⟩ : C))
      (a₂ := ⟨c*s,C.mul_mem hc hs⟩) ?_)
    change q (s*c) = q (c*s)
    simpa only [map_mul] using mem_center_iff.mp hcent (q s)
  refine ⟨c,hc,ho,?_,hcomm⟩
  rw [hprod]
  refine sup_le ?_ hCC
  intro v hv
  exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hV hv) c).symm

/-- Relative version: normalize R inside a two-group P and retain its full
central layer V and direct factor C. -/
theorem exists_relative_complement_involution_central_modulo
    (P R V C : Subgroup G) (hP : IsPGroup 2 P) (hRP : R ≤ P)
    (hPR : P ≤ normalizer (R : Set G)) (hPV : P ≤ centralizer (V : Set G))
    (hprod : R = V ⊔ C) (hdis : V ⊓ C = ⊥) (hne : C ≠ ⊥) :
    ∃ r : G, r ∈ C ∧ orderOf r = 2 ∧
      R ≤ centralizer ({r} : Set G) ∧ ⁅zpowers r,P⁆ ≤ V := by
  have hVR : V ≤ R := hprod.symm ▸ le_sup_left
  have hCR : C ≤ R := hprod.symm ▸ le_sup_right
  have hVP := hVR.trans hRP
  have hCP := hCR.trans hRP
  let : (R.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPR
  have hVZ : V.subgroupOf P ≤ center P := by
    intro v hv
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext ((hPV s.property) v hv).symm
  have hp : R.subgroupOf P = V.subgroupOf P ⊔ C.subgroupOf P := by
    rw [hprod,subgroupOf_sup hVP hCP]
  have hd : V.subgroupOf P ⊓ C.subgroupOf P = ⊥ := by
    apply bot_unique
    intro x hx
    exact Subtype.ext (hdis.le hx)
  have hn : C.subgroupOf P ≠ ⊥ := by
    intro hb
    have hh := congrArg (map P.subtype) hb
    exact hne (by simpa only [map_subgroupOf_eq_of_le hCP,Subgroup.map_bot] using hh)
  obtain ⟨r,hr,ho,hc,hm⟩ := exists_complement_involution_central_modulo
    hP (R.subgroupOf P) (V.subgroupOf P) (C.subgroupOf P) hVZ hp hd hn
  refine ⟨r,hr,(orderOf_coe r).trans ho,?_,?_⟩
  · intro s hs
    exact mem_centralizer_singleton_iff.mpr (congrArg P.subtype
      (mem_centralizer_singleton_iff.mp (hc (show (⟨s,hRP hs⟩ : P) ∈ R.subgroupOf P from hs))))
  · have hh := map_mono (f := P.subtype) hm
    rw [map_commutator,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le hVP,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh


/-- The full relative normalizer centralizes the moved irreducible direct
factor if every admissible complement involution has precisely kernel R. -/
theorem relative_normalizer_centralizes_irreducible_factor
    (P R V C F : Subgroup G) (hP : IsPGroup 2 P) (hRP : R < P)
    (hFP : F ≤ normalizer (P : Set G)) (hFR : F ≤ normalizer (R : Set G))
    (hFV : F ≤ normalizer (V : Set G))
    (hCV : C ≤ centralizer (V : Set G)) (hCF : C ≤ centralizer (F : Set G))
    (hprod : R = V ⊔ C) (hfix : V ⊓ centralizer (F : Set G) = ⊥)
    (hRne : R ≠ ⊥)
    (hirr : ∀ U : Subgroup G, U ≤ V → F ≤ normalizer (U : Set G) → U = ⊥ ∨ U = V)
    (hker : ∀ r : G, r ∈ C → orderOf r = 2 → R ≤ centralizer ({r} : Set G) →
      P ⊓ centralizer ({r} : Set G) = R) :
    R < P ⊓ normalizer (R : Set G) ∧
      P ⊓ normalizer (R : Set G) ≤ centralizer (V : Set G) := by
  let Q := P ⊓ normalizer (R : Set G)
  have hRQ : R ≤ Q := le_inf hRP.le R.le_normalizer
  have hgt : R < Q := by
    let : Group.IsNilpotent P := hP.isNilpotent
    have hproper : R.subgroupOf P < ⊤ := lt_top_iff_ne_top.mpr
      (fun he => hRP.not_ge (subgroupOf_eq_top.mp he))
    obtain ⟨s,hs,hsR⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (R.subgroupOf P) hproper)
    have hsN : (s : G) ∈ normalizer (R : Set G) := by
      rwa [←subgroupOf_normalizer_eq hRP.le] at hs
    refine lt_of_le_of_ne hRQ ?_
    intro he
    exact hsR (he.ge ⟨s.property,hsN⟩)
  have hFQ : F ≤ normalizer (Q : Set G) :=
    (le_inf hFP (hFR.trans (normalizer (R : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let E := R ⊓ centralizer (Q : Set G)
  have hEne : E ≠ ⊥ := by
    have hh := inf_centerIn_ne_bot (hP.to_le (show Q ≤ P from inf_le_left))
      hRne hRQ (show Q ≤ normalizer (R : Set G) from inf_le_right)
    intro he
    apply hh
    apply bot_unique
    exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans_eq he
  have hFE : F ≤ normalizer (E : Set G) :=
    (le_inf hFR (hFQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  have hproduct : (R : Set G) = (V : Set G) * (C : Set G) := by
    rw [hprod,coe_mul_of_right_le_normalizer_left V C
      (hCV.trans (centralizer_le_normalizer _))]
  have hRF : ⁅R,F⁆ ≤ V := by
    apply commutator_le.mpr
    intro r hr f hf
    obtain ⟨v,hv,c,hc,rfl⟩ := hproduct ▸ (show r ∈ (R : Set G) from hr)
    have hcf : ⁅c,f⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr ((hCF hc) f hf).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hcf,mul_one,mul_inv_cancel,one_mul]
    exact (le_normalizer_iff_commutator_le_left.mp hFV) (commutator_mem_commutator hv hf)
  have hEC : E ≤ centralizer (F : Set G) → E ≤ C := by
    intro he e heE
    obtain ⟨v,hv,c,hc,heq⟩ := hproduct ▸ heE.1
    have hvF : v ∈ centralizer (F : Set G) := by
      have hh := (centralizer (F : Set G)).mul_mem (he heE)
        ((centralizer (F : Set G)).inv_mem (hCF hc))
      rw [←heq,mul_inv_cancel_right] at hh
      exact hh
    have hv1 : v = 1 := hfix.le ⟨hv,hvF⟩
    have hec : e = c := by simpa only [hv1,one_mul] using heq.symm
    exact hec.symm ▸ hc
  have hmove : ⁅E,F⁆ ≠ ⊥ := by
    intro hb
    have hEC' := hEC (commutator_eq_bot_iff_le_centralizer.mp hb)
    have htwo : IsPGroup 2 E := hP.to_le (inf_le_left.trans hRP.le)
    obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G := E) 2
      (htwo.card_eq_or_dvd.resolve_left (fun hh => hEne (Subgroup.card_eq_one.mp hh)))
    have hQr : Q ≤ centralizer ({(r : G)} : Set G) := by
      intro q hq
      exact mem_centralizer_singleton_iff.mpr (r.property.2 q hq)
    have hk := hker r (hEC' r.property) ((orderOf_coe r).trans hr) (hRQ.trans hQr)
    exact hgt.not_ge ((le_inf (show Q ≤ P from inf_le_left) hQr).trans hk.le)
  have he := (hirr ⁅E,F⁆ ((commutator_mono inf_le_left le_rfl).trans hRF)
    (normalizer_commutator_ge_right E F)).resolve_left hmove
  refine ⟨hgt,?_⟩
  apply le_centralizer_iff.mp
  rw [←he]
  exact (le_normalizer_iff_commutator_le_left.mp hFE).trans inf_le_right

end Theory.GroupTheory
