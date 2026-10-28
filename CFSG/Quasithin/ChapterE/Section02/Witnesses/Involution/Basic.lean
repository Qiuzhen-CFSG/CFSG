module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.CoreFree
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Order-two witnesses in a core-free minimal parabolic

Baer–Suzuki supplies an odd-prime rotation inverted by the original
involution. Its rotation subgroup is disjoint from M: an inversion by
O₂(M) would otherwise force an odd element into O₂(M). The resulting
semidirect product is the actual join of two conjugates of V, with an
internal conjugator and the prescribed Sylow intersection. Its quotient
by the relative normal core is the required dihedral group.

Source: Aschbacher–Smith, E.2.7, printed p.218, the case |V| = 2.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Witnesses.Involution
variable {G : Type*} [Group G] [Finite G]

private theorem witness_of_inverted_line {p : ℕ} [Fact p.Prime]
    (M V : Subgroup G) [IsElementaryAbelian 2 V] (hVM : V ≤ M)
    (g v : G) (a : ℕ) (hv : v ∈ V) (ha : 0 < a) (hord : orderOf g = p^a)
    (ho : Odd (orderOf g)) (hg : g ≠ 1)
    (hi : v*g*v⁻¹ = g⁻¹) (hsign : ∀ w ∈ V, w*g*w⁻¹=g ∨ w*g*w⁻¹=g⁻¹)
    (hDM : Disjoint (zpowers g) M) : Nonempty (Solvable.CoreFreeWitness M V p) := by
  let D := zpowers g
  let I := D ⊔ V
  have hn := Theory.GroupTheory.normalizes_cyclic_of_identity_or_inversion V g hsign
  have hdM : Disjoint D M := hDM
  have hdV : Disjoint D V := hdM.mono_right hVM
  have hMI : M ⊓ I = V := by
    apply le_antisymm ?_ (le_inf hVM le_sup_right)
    intro x hx
    have hh : x ∈ (D : Set G) * (V : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left D V hn]
      exact hx.2
    obtain ⟨d,hd,w,hw,he⟩ := hh
    have hd' : d ∈ M := by
      have hh := M.mul_mem hx.1 (M.inv_mem (hVM hw))
      rwa [← he,mul_inv_cancel_right] at hh
    have hd1 := disjoint_def.mp hdM hd hd'
    have heq : w = x := by simpa only [hd1,one_mul] using he
    exact heq ▸ hw
  have hVle : V ≤ I := le_sup_right
  let U := V.subgroupOf I
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVle
  let gg : I := ⟨g,(show D ≤ I from le_sup_left) (mem_zpowers g)⟩
  let vv : I := ⟨v,hVle hv⟩
  have hgen : zpowers gg ⊔ U = ⊤ := by
    apply (map_injective I.subtype_injective)
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le hVle,
      ← MonoidHom.range_eq_map,range_subtype]
    rfl
  have hvU : vv ∈ U := hv
  have hi' : vv*gg*vv⁻¹=gg⁻¹ := Subtype.ext hi
  have hsign' : ∀w∈U,w*gg*w⁻¹=gg ∨ w*gg*w⁻¹=gg⁻¹ := by
    intro w hw
    rcases hsign w hw with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have ho' : Odd (orderOf gg) := by rwa [← Subgroup.orderOf_coe]
  have hg' : gg ≠ 1 := fun hh => hg (congrArg Subtype.val hh)
  have hcard : Nat.card I = orderOf g * Nat.card V := by
    simpa only [D,I,Nat.card_zpowers] using card_sup_eq_mul_of_normalizes_of_disjoint D V hn hdV
  have hidx : U.index = orderOf g := by
    have hh := U.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hVle).toEquiv,hcard] at hh
    have hpos : 0 < Nat.card V := Nat.card_pos
    nlinarith
  have hpU : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  let S : Sylow 2 I := hpU.toSylow (by rw [hidx]; exact ho.not_two_dvd_nat)
  have hM : M.subgroupOf I = U := by
    ext x
    exact ⟨fun hx => hMI.le ⟨hx,x.property⟩,fun hx => hVM hx⟩
  have hquot := Solvable.quotient_equiv_dihedral U gg vv hvU ho' hg' hgen hi' hsign'
  rw [← Subgroup.orderOf_coe,hord] at hquot
  refine ⟨⟨I,hVle,gg,?_,S,?_,hM,a,ha,?_⟩⟩
  · exact (Theory.GroupTheory.conjugate_join_eq_cyclic_sup U gg vv hvU ho' hi').trans hgen
  · exact map_subgroupOf_eq_of_le hVle
  · rwa [hM]

omit [Finite G] in
/-- The two-core of M cannot invert a nontrivial odd-prime rotation in M. -/
private theorem rotation_not_mem_of_inverter_in_core
    (M : Subgroup G) (v r : G) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hv : v ∈ (pCore 2 M).map M.subtype) (hr : orderOf r = p)
    (hi : v*r*v⁻¹=r⁻¹) : r ∉ M := by
  intro hrM
  obtain ⟨vv,hvv,hvvG⟩ := hv
  let rr : M := ⟨r,hrM⟩
  have hcomm : rr*vv*rr⁻¹*vv⁻¹ ∈ pCore 2 M :=
    (pCore 2 M).mul_mem ((inferInstance : (pCore 2 M).Normal).conj_mem vv hvv rr)
      ((pCore 2 M).inv_mem hvv)
  have hi' : vv*rr*vv⁻¹=rr⁻¹ := by
    apply Subtype.ext
    change (vv:G)*r*(vv:G)⁻¹=r⁻¹
    change (vv:G)=v at hvvG
    rw [hvvG]
    exact hi
  have hrr : orderOf rr = p := by
    rw [← Subgroup.orderOf_coe]
    exact hr
  have he : rr*vv*rr⁻¹*vv⁻¹=rr^2 := by
    have h := congrArg Inv.inv hi'
    have hh : vv*rr⁻¹*vv⁻¹=rr := by simpa only [mul_inv_rev,inv_inv,mul_assoc] using h
    rw [mul_assoc rr vv,mul_assoc rr,hh,pow_two]
  rw [he] at hcomm
  have hpr : IsPGroup p (zpowers rr) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers,pow_one] using hrr)
  have hd : Disjoint (zpowers rr) (pCore 2 M) :=
    hpr.disjoint_of_coprime pCore_isPGroup
      (Nat.coprime_two_right.mpr ((Fact.out : p.Prime).odd_of_ne_two hp))
  have hsq : rr^2=1 := disjoint_def.mp hd (pow_mem (mem_zpowers rr) 2) hcomm
  have hpdiv : p ∣ 2 := by
    have hh := orderOf_dvd_of_pow_eq_one hsq
    simpa only [hrr] using hh
  exact hp (((Nat.dvd_prime Nat.prime_two).mp hpdiv).resolve_left (Fact.out : p.Prime).ne_one)

/-- Every original order-two V outside O₂(G) has a genuine dihedral source pair. -/
theorem exists_dihedral_of_card_two (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hcore : V ≤ (pCore 2 M).map M.subtype) (hcard : Nat.card V = 2)
    (hout : ¬ V ≤ pCore 2 G) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (Solvable.CoreFreeWitness M V p) := by
  obtain ⟨v,hv,hvout⟩ := SetLike.not_le_iff_exists.mp hout
  have hv1 : v ≠ 1 := fun h => hvout (h ▸ one_mem _)
  have hv2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
  have hinv : BenderSuzuki.PFAppendixIII.IsInvolution v := ⟨hv1,hv2⟩
  obtain ⟨p,hp,hp2,r,hr,hi⟩ := BenderSuzuki.involution_outside_twoCore_inverts_odd_prime v hinv hvout
  let : Fact p.Prime := ⟨hp⟩
  have hi' : v*r*v⁻¹=r⁻¹ := by
    simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem,hinv.inv_eq_self] using hi
  have hrM := rotation_not_mem_of_inverter_in_core M v r hp2 (hcore hv) hr hi'
  have hd : Disjoint (zpowers r) M := (M.disjoint_zpowers_of_prime_order_not_mem r hr hrM).symm
  have hsign : ∀ w∈V,w*r*w⁻¹=r ∨ w*r*w⁻¹=r⁻¹ := by
    intro w hw
    by_cases h : w=1
    · left; simp only [h,one_mul,inv_one,mul_one]
    · have he : w=v := by
        obtain ⟨x,hx,hu⟩ := (Nat.card_eq_two_iff' (1:V)).mp hcard
        exact congrArg Subtype.val ((hu ⟨w,hw⟩ (fun he => h (congrArg Subtype.val he))).trans
          (hu ⟨v,hv⟩ (fun he => hv1 (congrArg Subtype.val he))).symm)
      exact Or.inr (he ▸ hi')
  refine ⟨p,hp,hp2,?_⟩
  exact witness_of_inverted_line M V (hcore.trans (map_subtype_le _)) r v 1 hv
    (by decide) (by simpa only [pow_one] using hr)
    (hr ▸ hp.odd_of_ne_two hp2)
    (fun h => hp.ne_one (hr.symm.trans (h ▸ orderOf_one))) hi' hsign hd
/-- Attach the original ambient Sylow to the constructed dihedral pair. -/
theorem exists_pair_of_card_two (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hcore : V ≤ (pCore 2 M).map M.subtype) (hcard : Nat.card V = 2)
    (hout : ¬ V ≤ pCore 2 G) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ w : QuotientLift.Pair T M V,
      ∃ a : ℕ, 0 < a ∧ Nonempty ((w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore) ≃*
        DihedralGroup (p^a)) ∧ M.subgroupOf w.subgroup = V.subgroupOf w.subgroup := by
  obtain ⟨p,hp,hp2,⟨w⟩⟩ := exists_dihedral_of_card_two M V hcore hcard hout
  have hTS : (T : Subgroup G).subgroupOf w.subgroup = w.sylow := by
    apply w.sylow.is_maximal' T.isPGroup'.comap_subtype
    intro x hx
    have hV : (x:G) ∈ (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype :=
      mem_map_of_mem w.subgroup.subtype hx
    rw [w.sylow_eq] at hV
    exact hVT hV
  have hmap : (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype =
      (T : Subgroup G) ⊓ w.subgroup := by
    rw [← hTS,subgroupOf_map_subtype]
  have htwo : IsPGroup 2 (M.subgroupOf w.subgroup).normalCore := by
    rw [w.maximal_eq]
    exact ((IsElementaryAbelian.isPGroup 2 V).comap_subtype).to_le (normalCore_le _)
  have hclosed : ∃S : Sylow 2 (M.subgroupOf w.subgroup).normalCore,
      (S : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal := by
    refine ⟨(htwo.to_subgroup ⊤).toSylow (by simp),?_⟩
    exact inferInstanceAs (⊤ : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal
  let ww : QuotientLift.Pair T M V :=
    ⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,hmap,hclosed⟩
  exact ⟨p,hp,hp2,ww,w.exponent,w.positive,w.dihedral,w.maximal_eq⟩

/-- Original E.2.7 when the elementary subgroup has order two; no group model is needed. -/
theorem source_order_two (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup G)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hcard : Nat.card V = 2) (hJ : ChapterB.minimalParabolicCore T hP = ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ w : QuotientLift.Pair T (ChapterB.minimalParabolicMax T hP) V,
      ∃ a : ℕ, 0 < a ∧ Nonempty ((w.subgroup ⧸
        ((ChapterB.minimalParabolicMax T hP).subgroupOf w.subgroup).normalCore) ≃*
        DihedralGroup (p^a)) := by
  have hO : pCore 2 G = ⊥ := bot_unique (hJ ▸ ChapterB.minimalParabolicTwoCore_le_core T hP)
  have hout : ¬ V ≤ pCore 2 G := by
    intro h
    have he : V = ⊥ := bot_unique (hO ▸ h)
    have hc := Subgroup.card_eq_one.mpr he
    omega
  obtain ⟨p,hp,hp2,w,a,ha,he,_⟩ := exists_pair_of_card_two T _ V hVT hcore hcard hout
  exact ⟨p,hp,hp2,w,a,ha,he⟩
end CFSG.Quasithin.ChapterE.Witnesses.Involution
