module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.CubicOvergroups
public import Theory.Representation.FirstCohomologyInflationDetection

/-!
# Constructing the original outer involution

The squared L-displacements of an element of C_Q(X₁) form a cocycle on
 the actual natural L/P module. A nontrivial involution coming from
 [U,X₁] detects its cohomology class. Its principal vector lies in V₁,
 so a square root in the original Z(U) adjusts the element while keeping
 it in C_Q(X₁)−L. All adjusted displacements lie in V. Since the element
 fixes V, its square centralizes L, and C_T(L)=1 makes it an involution.

Source: Aschbacher--Smith, 14.3.33(3), printed p.1005, the Gaschütz
 adjustment and subsequent involution construction.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Fixing the original seed makes the L-displacements lie in P. -/
theorem seed_centralizer_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (c : G) (hcT : c ∈ T) (hcV : c ∈ centralizer (V : Set G))
    (l : G) (hl : l ∈ L) : ⁅c,l⁆ ∈ L.pCoreIn 2 := by
  have hc : ⁅c,l⁆ ∈ centralizer (V : Set G) := by
    have hn := (normalizer_le_normalizer_centralizer V) (h.chosen.normalizes hl)
    have hh := (centralizer (V : Set G)).mul_mem hcV
      ((mem_normalizer_iff.mp hn c⁻¹).mp ((centralizer _).inv_mem hcV))
    simpa only [commutatorElement_def, mul_assoc] using hh
  have hL : ⁅c,l⁆ ∈ L := L.mul_mem
    ((mem_normalizer_iff.mp (h.sylow_normalizes_at structural hcT) l).mp hl) (L.inv_mem hl)
  exact h.centralizer_L ▸ ⟨hL,hc⟩

/-- The squared displacement on the original natural module is principal.
The detecting involution comes from [U,X₁], which the original c centralizes. -/
theorem cubic_centralizer_square_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (c : G) (hc : c ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) :
    ∃ v : G, v ∈ F.Vi 1 ∧ ∀ l ∈ L, ⁅c,l⁆ ^ 2 = l * v * l⁻¹ * v⁻¹ := by
  let := h.chosen.elementary
  have heP := centerSpan_eq_core h structural alternatives F s hne
  let := centerSpan_abelian h structural F s
  have hcomm (a b : G) (ha : a ∈ L.pCoreIn 2) (hb : b ∈ L.pCoreIn 2) : Commute a b :=
    congrArg Subtype.val (mul_comm (⟨a,heP.symm ▸ ha⟩ : centerSpan L F) ⟨b,heP.symm ▸ hb⟩)
  have hPN : L ≤ normalizer (L.pCoreIn 2 : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hcT := point_core_le_sylow F hc.1
  have hcV := h.chosen.core_centralizes
    (core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 hc)
  have hd (l : L) : ⁅c,(l : G)⁆ ∈ L.pCoreIn 2 :=
    seed_centralizer_displacement h structural c hcT hcV l l.property
  have hs (l : L) : ⁅c,(l : G)⁆ ^ 2 ∈ V :=
    centerSpan_square_mem_seed h structural F s (heP.symm ▸ hd l)
  let d (l : L) : V := ⟨⁅c,(l : G)⁆ ^ 2,hs l⟩
  let e := h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let b : V ≃* Multiplicative (Fin 3 → ZMod 2) :=
    h.naturalMarking.coordinates.toAddEquiv.toMultiplicativeRight
  let ρ := Representation.specialLinearNatural (k := ZMod 2) 3
  have hb (l : L) (v : V) :
      (b (setupSeedAction L V h.chosen.normalizes l v)).toAdd = ρ (f l) (b v).toAdd := by
    have hv := h.naturalMarking.equivariant l (Additive.ofMul v)
    have he := congrArg (fun a : BinaryLinear.OuterCyclic.LinearGroup 3 => a (b v).toAdd)
      ((BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply
        (h.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)))
    exact hv.trans he.symm
  have hdmul (l t : L) : d (l*t) = setupSeedAction L V h.chosen.normalizes l (d t) * d l := by
    apply Subtype.ext
    change ⁅c,(l:G)*(t:G)⁆ ^ 2 = (l:G) * ⁅c,(t:G)⁆ ^ 2 * (l:G)⁻¹ * ⁅c,(l:G)⁆ ^ 2
    have hp : (l:G) * ⁅c,(t:G)⁆ * (l:G)⁻¹ ∈ L.pCoreIn 2 :=
      (mem_normalizer_iff.mp (hPN l.property) _).mp (hd t)
    have he : ⁅c,(l:G)*(t:G)⁆ = ⁅c,(l:G)⁆ * ((l:G)*⁅c,(t:G)⁆*(l:G)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [he, (hcomm _ _ (hd l) hp).eq, (hcomm _ _ hp (hd l)).mul_pow]
    rw [conj_pow]
  let z : Representation.OneCohomology.cocycles (ρ.comp f) := ⟨fun l => (b (d l)).toAdd,by
    intro l t
    change (b (d (l*t))).toAdd = ρ (f l) (b (d t)).toAdd + (b (d l)).toAdd
    rw [hdmul, map_mul, toAdd_mul, hb]⟩
  have hzero : ∀ n ∈ f.ker, z.val n = 0 := by
    intro n hn
    have hnP : (n:G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype (hk ▸ hn)
    have hnV := centerSpan_square_mem_seed h structural F s (heP.symm ▸ hnP)
    have hcn : c * (n:G) * c⁻¹ ∈ L.pCoreIn 2 :=
      (mem_normalizer_iff.mp ((normalizer_le_normalizer_characteristic_image L (pCore 2 L))
        (h.sylow_normalizes_at structural hcT)) _).mp hnP
    have he : ⁅c,(n:G)⁆ ^ 2 = 1 := by
      change (c*(n:G)*c⁻¹ * (n:G)⁻¹)^2 = 1
      rw [(hcomm _ _ hcn ((L.pCoreIn 2).inv_mem hnP)).mul_pow]
      rw [conj_pow]
      rw [← hcV _ hnV, mul_inv_cancel_right, inv_pow, mul_inv_cancel]
    have hd1 : d n = 1 := Subtype.ext he
    change (b (d n)).toAdd = 0
    rw [hd1,map_one]
    rfl
  have hnot : ¬ ⁅F.U,zpowers x⁆ ≤ L.pCoreIn 2 := by
    intro hh
    have hu : F.U ≤ L.pCoreIn 2 := by
      rw [closure_cubic_decomposition F s x (F.Li_le L 1 hx).2 hx3]
      exact sup_le hh ((le_conjugateSpanBy F.ZU L).trans heP.le)
    have hi := centerSpan_inf_closure_card h structural alternatives F s hne
    rw [heP,inf_eq_right.mpr hu,s.core_shape.card] at hi
    omega
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hnot
  have haU : a ∈ F.U := (le_normalizer_iff_commutator_le_left.mp
    ((zpowers_le.mpr (F.Li_le L 1 hx).2).trans (le_normalizer_conjugateSpanBy V F.H))) ha
  let aL : L := ⟨a,closure_le_actor h structural alternatives F s hne haU⟩
  have ha1 : f aL ≠ 1 := by
    intro he
    exact han (mem_map_of_mem L.subtype (hk ▸ (show aL ∈ f.ker from he)))
  have ha2 : f aL * f aL = 1 := by
    rw [← map_mul]
    apply MonoidHom.mem_ker.mp
    rw [hk]
    let : Fact (IsPGroup 2 F.U) := ⟨IsPGroup.of_card (n := 6) s.core_shape.card⟩
    have hh := mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨a,haU⟩ : F.U))
    rw [closure_frattini h structural alternatives F hne] at hh
    have hp := ((seed_le_centerSpan h F).trans heP.le) (F.le_seed 1 hh)
    obtain ⟨v,hv,hev⟩ := hp
    change (v:G) = a^2 at hev
    have he' : v = aL*aL := by
      apply Subtype.ext
      change (v:G) = a*a
      simpa only [pow_two] using hev
    exact he' ▸ hv
  have haz : z.val aL = 0 := by
    have hh := core_cubic_centralizes_commutator F s x (F.Li_le L 1 hx).2 hx3 hc a ha
    have he : ⁅c,a⁆ = 1 := by
      rw [commutatorElement_def,← hh,mul_inv_cancel_right,mul_inv_cancel]
    have hd1 : d aL = 1 := Subtype.ext (by change ⁅c,a⁆^2 = 1; rw [he,one_pow])
    change (b (d aL)).toAdd = 0
    rw [hd1,map_one]
    rfl
  obtain ⟨w,hw⟩ := Representation.OneCohomology.principal_of_surjective_of_zero_kernel f hf ρ z hzero aL haz
    (fun z hz => Representation.OneCohomology.SLHigherNatural.SLThreeBinary.principal_of_zero_involution
      z (f aL) ha1 ha2 hz)
  let v := b.symm (Multiplicative.ofAdd w)
  have hv (l : L) : (d l : G) = (l:G) * (v:G) * (l:G)⁻¹ * (v:G)⁻¹ := by
    have he : d l = setupSeedAction L V h.chosen.normalizes l v * v⁻¹ := by
      apply b.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,hb]
      have hvw : (b v).toAdd = w := congrArg Multiplicative.toAdd (b.apply_symm_apply _)
      rw [hvw]
      simpa only [sub_eq_add_neg] using hw l
    exact congrArg Subtype.val he
  have hxv : (v:G) ∈ F.ZU := by
    rw [← closure_cubic_centralizer F s x (F.Li_le L 1 hx).2 hx3]
    refine ⟨le_conjugateSpanBy V F.H v.property,?_⟩
    rw [zpowers_eq_closure,centralizer_closure]
    change (v:G) ∈ centralizer ({x} : Set G)
    apply mem_centralizer_singleton_iff.mpr
    have hh := hv ⟨x,(F.Li_le L 1 hx).1⟩
    have hcx : ⁅c,x⁆ = 1 := by
      rw [commutatorElement_def,← hc.2 x (mem_zpowers x),mul_inv_cancel_right,mul_inv_cancel]
    change ⁅c,x⁆^2 = _ at hh
    rw [hcx,one_pow] at hh
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hh.symm)).symm
  let := F.localKernel_tilde_seed_elementary
  refine ⟨v,?_,fun l hl => hv ⟨l,hl⟩⟩
  rw [← F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne]
  exact ⟨v.property,hxv⟩

/-- The original order-eight cubic centralizer contains an outer involution
whose L-displacements lie in the original seed. The adjustment stays in Z(U). -/
theorem exists_outer_involution
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8) :
    ∃ r : G, r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ∧ r ∉ L ∧
      orderOf r = 2 ∧ ∀ l ∈ L, ⁅r,l⁆ ∈ V := by
  let := h.chosen.elementary
  let C := F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)
  have heP := centerSpan_eq_core h structural alternatives F s hne
  let := centerSpan_abelian h structural F s
  have hcomm (a b : G) (ha : a ∈ L.pCoreIn 2) (hb : b ∈ L.pCoreIn 2) : Commute a b :=
    congrArg Subtype.val (mul_comm (⟨a,heP.symm ▸ ha⟩ : centerSpan L F) ⟨b,heP.symm ▸ hb⟩)
  have hZC : F.ZU ≤ C := (point_core_cubic_supplement h structural alternatives F s hne x hx hx3).2.symm.le.trans inf_le_right
  have hZP : F.ZU ≤ L.pCoreIn 2 := (le_conjugateSpanBy F.ZU L).trans heP.le
  have hnot : ¬ C ≤ F.ZU := by
    intro hh
    obtain ⟨e⟩ := center_model F s
    have hz : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
    have hc := card_le_of_le hh
    rw [show Nat.card C = 8 from hcard,hz] at hc
    omega
  obtain ⟨c,hc,hcn⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨v,hv,hdis⟩ := cubic_centralizer_square_displacement h structural alternatives F s hne x hx hx3 c hc
  have hsq : v ∈ (centralSquares F.U).map F.U.subtype := (center_squares_eq_point h F s).symm ▸ hv
  obtain ⟨a,ha,he⟩ := hsq
  obtain ⟨z,hz⟩ := mem_centralSquares.mp ha
  let zG : G := z.val
  have hzZ : zG ∈ F.ZU := mem_map_of_mem F.U.subtype z.property
  have hz2 : zG^2 = v := (congrArg Subtype.val hz).trans he
  let r := zG * c
  have hrC : r ∈ C := C.mul_mem (hZC hzZ) hc
  have hrL : r ∉ L := by
    intro hh
    have hrZ : r ∈ F.ZU := core_cubic_centralizer_inter_actor h structural alternatives F s hne x hx hx3 ▸ ⟨hh,hrC⟩
    have hh := F.ZU.mul_mem (F.ZU.inv_mem hzZ) hrZ
    exact hcn (by simpa only [r,inv_mul_cancel_left] using hh)
  have hcT := point_core_le_sylow F hc.1
  have hcV := h.chosen.core_centralizes
    (core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 hc)
  have hrT := point_core_le_sylow F hrC.1
  have hrV := h.chosen.core_centralizes
    (core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 hrC)
  have hrdis (l : G) (hl : l ∈ L) : ⁅r,l⁆ ∈ V := by
    have hdP := seed_centralizer_displacement h structural c hcT hcV l hl
    have hzlP : l*zG*l⁻¹ ∈ L.pCoreIn 2 :=
      (mem_normalizer_iff.mp ((L.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) hl) _).mp (hZP hzZ)
    have hzd : ⁅zG,l⁆ ∈ L.pCoreIn 2 := by
      have hh := (L.pCoreIn 2).mul_mem (hZP hzZ) ((L.pCoreIn 2).inv_mem hzlP)
      simpa only [commutatorElement_def,mul_inv_rev,inv_inv,mul_assoc] using hh
    have hd : ⁅r,l⁆ = ⁅c,l⁆ * ⁅zG,l⁆ := by
      calc
        ⁅r,l⁆ = zG * ⁅c,l⁆ * zG⁻¹ * ⁅zG,l⁆ := by
          simp only [r,commutatorElement_def]
          group
        _ = ⁅c,l⁆ * ⁅zG,l⁆ := by rw [(hcomm _ _ (hZP hzZ) hdP).eq,mul_inv_cancel_right]
    have hzd2 : ⁅zG,l⁆^2 = v*l*v⁻¹*l⁻¹ := by
      have he : ⁅zG,l⁆ = zG * (l*zG*l⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [he,(hcomm _ _ (hZP hzZ) ((L.pCoreIn 2).inv_mem hzlP)).mul_pow,inv_pow,
        conj_pow]
      change zG^2 * (l*zG^2*l⁻¹)⁻¹ = _
      rw [hz2]
      group
    have hs : ⁅r,l⁆^2 = 1 := by
      rw [hd,(hcomm _ _ hdP hzd).mul_pow,hdis l hl,hzd2]
      group
    exact (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 _
      (heP.symm ▸ seed_centralizer_displacement h structural r hrT hrV l hl) |>.mp hs
  have hr2 : r^2 = 1 := by
    apply mem_bot.mp
    rw [← sylow_actor_centralizer_eq_bot h structural alternatives F s hne]
    refine ⟨(T : Subgroup G).pow_mem hrT 2,?_⟩
    intro l hl
    have hc : Commute r ⁅r,l⁆ := (hrV _ (hrdis l hl)).symm
    have hsq : ⁅r^2,l⁆ = 1 := by
      calc
        ⁅r^2,l⁆ = r * ⁅r,l⁆ * r⁻¹ * ⁅r,l⁆ := by simp only [commutatorElement_def,pow_two]; group
        _ = ⁅r,l⁆^2 := by rw [hc.eq,mul_inv_cancel_right,pow_two]
        _ = 1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) _ (hrdis l hl)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hsq).symm
  exact ⟨r,hrC,hrL,orderOf_eq_prime hr2 (fun he => hrL (he ▸ L.one_mem)),hrdis⟩


end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
