module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterClosureFusion

/-!
# Sylow centralizers of the original outer involution

The factorization L=P C_L(r) restricts to T intersect L, giving an
inner centralizer of order 64. The original index-two extension then
splits over the actual involution r, so its full Sylow centralizer has
order 128. Its central Frattini subgroup lies in the original point V₁:
Frattini elements lie in L, central elements centralize V, and the
factorization forces the resulting elements of V to centralize U.

Source: Aschbacher--Smith, 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual inner Sylow factors through P and its centralizer of r. -/
theorem outer_involution_inner_sylow_factorization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V) :
    (T : Subgroup G) ⊓ L = L.pCoreIn 2 ⊔
      ((T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G)) := by
  have hPT := (show L.pCoreIn 2 ≤ L.pCoreIn 2 ⊔ F.U from le_sup_left).trans
    (core_closure_le_sylow h structural F s)
  obtain ⟨hfac,_⟩ := outer_involution_actor_factorization h structural alternatives F s hne
    x hx hx3 r hr hrL hdis
  have hn : L ⊓ centralizer ({r} : Set G) ≤ normalizer (L.pCoreIn 2 : Set G) :=
    inf_le_left.trans (L.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  apply le_antisymm ?_ (sup_le (le_inf hPT (pCoreIn_le 2 L)) inf_le_left)
  rintro l ⟨hlT,hlL⟩
  have hl : l ∈ (L.pCoreIn 2 : Set G) * ((L ⊓ centralizer ({r} : Set G) : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn,←hfac]
    exact hlL
  obtain ⟨p,hp,c,hc,rfl⟩ := hl
  have hcT : c ∈ (T : Subgroup G) := by
    have hh := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hPT hp)) hlT
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem_sup hp ⟨⟨hcT,hc.1⟩,hc.2⟩

/-- The inner Sylow centralizer has order 64, using P intersect C_L(r)=V. -/
theorem outer_involution_inner_sylow_centralizer_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V) :
    Nat.card ((T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G) : Subgroup G) = 64 := by
  have hPT := (show L.pCoreIn 2 ≤ L.pCoreIn 2 ⊔ F.U from le_sup_left).trans
    (core_closure_le_sylow h structural F s)
  have hi : L.pCoreIn 2 ⊓ ((T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G)) = V := by
    rw [←(outer_involution_actor_factorization h structural alternatives F s hne x hx hx3 r hr hrL hdis).2]
    ext a
    exact ⟨fun ha => ⟨ha.1,ha.2.2⟩,
      fun ha => ⟨ha.1,⟨hPT ha.1,pCoreIn_le 2 L ha.1⟩,ha.2⟩⟩
  have hn : (T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G) ≤ normalizer (L.pCoreIn 2 : Set G) :=
    (inf_le_left.trans inf_le_right).trans (L.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (L.pCoreIn 2)
    ((T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G)) hn
  have hp : Nat.card (L.pCoreIn 2) = 64 :=
    (centerSpan_eq_core h structural alternatives F s hne) ▸
      (centerSpan_square_kernel_and_card h structural alternatives F s hne).2
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [hp,hi,hv,←outer_involution_inner_sylow_factorization h structural alternatives F s hne
    x hx hx3 r hr hrL hdis,sylow_inter_actor_card h structural alternatives F s hne] at hh
  omega

/-- The actual outside involution supplements T intersect L in T. -/
theorem outer_involution_sylow_factorization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hr2 : orderOf r = 2) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔ zpowers r := by
  classical
  let := h.chosen.elementary
  have hrT := point_core_le_sylow F hr.1
  have hn : zpowers r ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (zpowers_le.mpr hrT).trans
      ((le_inf (T : Subgroup G).le_normalizer (h.sylow_normalizes_at structural)).trans
        inf_normalizer_le_normalizer_inf)
  have hi : (T : Subgroup G) ⊓ L ⊓ zpowers r = ⊥ := by
    apply eq_bot_iff.mpr
    rintro a ⟨ha,har⟩
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp har)
    have hi : i < 2 := by simpa [hr2] using hi
    interval_cases i
    · simpa using he.symm
    · apply False.elim
      apply hrL
      rw [show r = a by simpa only [pow_one] using he]
      exact ha.2
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    ((T : Subgroup G) ⊓ L) (zpowers r) hn
  rw [sylow_inter_actor_card h structural alternatives F s hne,Nat.card_zpowers,hr2,hi,
    Nat.card_unique,one_mul] at hh
  have hQ : Nat.card (F.H.pCoreIn 2) = 128 := by
    rw [point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives F s hne x hx hx3,hcard]
  have hT := sylow_card_of_point_core_card F s hQ
  exact (eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr hrT)) (by omega)).symm

/-- The full Sylow centralizer is the product of its inner part and the actual r. -/
theorem outer_involution_sylow_centralizer_factorization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hr2 : orderOf r = 2) :
    (T : Subgroup G) ⊓ centralizer ({r} : Set G) =
      ((T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G)) ⊔ zpowers r := by
  let := h.chosen.elementary
  have hrT := point_core_le_sylow F hr.1
  have hRC : zpowers r ≤ centralizer ({r} : Set G) := zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr rfl)
  have hn : zpowers r ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (zpowers_le.mpr hrT).trans
      ((le_inf (T : Subgroup G).le_normalizer (h.sylow_normalizes_at structural)).trans
        inf_normalizer_le_normalizer_inf)
  apply le_antisymm ?_ (sup_le (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (zpowers_le.mpr hrT) hRC))
  rintro a ⟨haT,haC⟩
  have ha : a ∈ (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) * (zpowers r : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn,
      ←outer_involution_sylow_factorization h structural alternatives F s hne x hx hx3 hcard r hr hrL hr2]
    exact haT
  obtain ⟨l,hl,b,hb,rfl⟩ := ha
  have hlC : l ∈ centralizer ({r} : Set G) := by
    have hh := (centralizer ({r} : Set G)).mul_mem haC ((centralizer _).inv_mem (hRC hb))
    simpa only [mul_inv_cancel_right] using hh
  exact mul_mem_sup ⟨hl,hlC⟩ hb

/-- The outer involution has Sylow centralizer of order 128. -/
theorem outer_involution_sylow_centralizer_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hr2 : orderOf r = 2) (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({r} : Set G) : Subgroup G) = 128 := by
  classical
  let A := (T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G)
  have hRA : zpowers r ≤ centralizer (A : Set G) := by
    apply zpowers_le.mpr
    intro a ha
    exact mem_centralizer_singleton_iff.mp ha.2
  have hi : A ⊓ zpowers r = ⊥ := by
    apply eq_bot_iff.mpr
    rintro a ⟨ha,har⟩
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp har)
    have hi : i < 2 := by simpa [hr2] using hi
    interval_cases i
    · simpa using he.symm
    · apply False.elim
      apply hrL
      rw [show r = a by simpa only [pow_one] using he]
      exact ha.1.2
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A (zpowers r)
    (hRA.trans (Subgroup.centralizer_le_normalizer _))
  have hcA : Nat.card A = 64 := outer_involution_inner_sylow_centralizer_card h structural alternatives
    F s hne x hx hx3 r hr hrL hdis
  rw [hcA,Nat.card_zpowers,hr2,hi,Subgroup.card_bot,one_mul] at hh
  rw [outer_involution_sylow_centralizer_factorization h structural alternatives F s hne
    x hx hx3 hcard r hr hrL hr2]
  exact hh.symm

/-- The central Frattini subgroup of C_T(r) lies in the original point V₁. -/
theorem outer_involution_central_frattini_le_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hr2 : orderOf r = 2) (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V) :
    let C := (T : Subgroup G) ⊓ centralizer ({r} : Set G)
    Chapter12.Section08.centerIn C ⊓ (frattini C).map C.subtype ≤ F.Vi 1 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let := centerSpan_abelian h structural F s
  let C := (T : Subgroup G) ⊓ centralizer ({r} : Set G)
  let A := (T : Subgroup G) ⊓ L ⊓ centralizer ({r} : Set G)
  have hAC : A ≤ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hLC : L.subgroupOf C = A.subgroupOf C := by
    ext a
    exact ⟨fun ha => ⟨⟨a.property.1,ha⟩,a.property.2⟩,fun ha => ha.1.2⟩
  have hLA : Nat.card (L.subgroupOf C) = 64 := by
    rw [hLC,Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
    exact outer_involution_inner_sylow_centralizer_card h structural alternatives F s hne
      x hx hx3 r hr hrL hdis
  have hC : Nat.card C = 128 := outer_involution_sylow_centralizer_card h structural alternatives F s hne
    x hx hx3 hcard r hr hrL hr2 hdis
  have hindex : (L.subgroupOf C).index = 2 := by
    have hh := (L.subgroupOf C).card_mul_index
    rw [hLA,hC] at hh
    omega
  have hmax : IsCoatom (L.subgroupOf C) := by
    refine ⟨fun ht => by simp [ht] at hindex,fun B hB => ?_⟩
    have hm := relIndex_mul_index hB.le
    rw [hindex] at hm
    have hp : ((L.subgroupOf C).relIndex B * B.index).Prime := hm ▸ Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hBtop⟩ | ⟨_,hr⟩
    · exact index_eq_one.mp hBtop
    · exact (hB.not_ge (relIndex_eq_one.mp hr)).elim
  have hphiL : (frattini C).map C.subtype ≤ L := by
    rintro a ⟨b,hb,rfl⟩
    exact frattini_le_coatom hmax hb
  have heP := centerSpan_eq_core h structural alternatives F s hne
  have hVP := (seed_le_centerSpan h F).trans heP.le
  have hrV := h.chosen.core_centralizes
    (core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 hr)
  have hVC : V ≤ C := le_inf h.chosen.le_sylow (fun v hv =>
    mem_centralizer_singleton_iff.mpr (hrV v hv))
  change Chapter12.Section08.centerIn C ⊓ (frattini C).map C.subtype ≤ F.Vi 1
  rintro a ⟨haZ,haPhi⟩
  have haC : a ∈ centralizer (C : Set G) := centerIn_le_centralizer C haZ
  have haP : a ∈ L.pCoreIn 2 := h.centralizer_L ▸
    ⟨hphiL haPhi,centralizer_le hVC haC⟩
  have haV : a ∈ V :=
    (outer_involution_actor_factorization h structural alternatives F s hne x hx hx3 r hr hrL hdis).2 ▸
      ⟨haP,(map_subtype_le (center C) haZ).2⟩
  have haCP : a ∈ centralizer (L.pCoreIn 2 : Set G) := by
    intro p hp
    exact congrArg Subtype.val (mul_comm (⟨p,heP.symm ▸ hp⟩ : centerSpan L F)
      ⟨a,heP.symm ▸ haP⟩)
  have haCTL : a ∈ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [outer_involution_inner_sylow_factorization h structural alternatives F s hne x hx hx3 r hr hrL hdis]
    exact (le_centralizer_iff.mp (sup_le (le_centralizer_iff.mpr (zpowers_le.mpr haCP))
      (le_centralizer_iff.mpr (zpowers_le.mpr (centralizer_le hAC haC))))) (mem_zpowers a)
  have hUTL : F.U ≤ (T : Subgroup G) ⊓ L :=
    le_inf (closure_le_sylow F s) (closure_le_actor h structural alternatives F s hne)
  have haZU : a ∈ F.ZU := by
    rw [ZU,centerIn_eq_inf_centralizer]
    exact ⟨le_conjugateSpanBy V F.H haV,centralizer_le hUTL haCTL⟩
  rw [← F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne]
  exact ⟨haV,haZU⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
