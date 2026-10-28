module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterDisplacement

/-!
# The original outer involution and the homocyclic core

An element of C_Q(X₁) outside L acts nontrivially on the cyclic Z(U),
 hence inverts it. Its displacements in the abelian P show that this
 inversion extends to the entire L-span P. Square roots in P then give
 L=P C_L(r), with P∩C_L(r)=V. The inclusion induces the literal
 C_L(r)/V≃L/P, and |C_L(r)|=1344. The outer branch also has
 |T:T∩L|=2, for the subsequent ambient transfer.

Source: Aschbacher--Smith, 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every outer element of the original cubic centralizer inverts the cyclic
center and hence its entire L-span P. -/
theorem outer_cubic_inverts_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L) :
    ∀ p ∈ L.pCoreIn 2, r*p*r⁻¹ = p⁻¹ := by
  let := h.chosen.elementary
  have heP := centerSpan_eq_core h structural alternatives F s hne
  let := centerSpan_abelian h structural F s
  have hcomm (a b : G) (ha : a ∈ L.pCoreIn 2) (hb : b ∈ L.pCoreIn 2) : Commute a b :=
    congrArg Subtype.val (mul_comm (⟨a,heP.symm ▸ ha⟩ : centerSpan L F) ⟨b,heP.symm ▸ hb⟩)
  have hZP : F.ZU ≤ L.pCoreIn 2 := (le_conjugateSpanBy F.ZU L).trans heP.le
  have hrN : r ∈ normalizer (F.ZU : Set G) := F.H_normalizes_ZU (pCoreIn_le 2 F.H hr.1)
  obtain ⟨e⟩ := center_model F s
  let := e.isCyclic.mpr inferInstance
  let := IsCyclic.commGroup (α := F.ZU)
  let α : MulAut F.ZU := F.ZU.normalizerMonoidHom ⟨r,hrN⟩
  let β : MulAut F.ZU :=
    { toFun := Inv.inv
      invFun := Inv.inv
      left_inv := inv_inv
      right_inv := inv_inv
      map_mul' := fun a b => by rw [mul_inv_rev,mul_comm] }
  have hα : α ≠ 1 := by
    intro hh
    have hcz : r ∈ centralizer (F.ZU : Set G) := by
      have hk : (⟨r,hrN⟩ : normalizer (F.ZU : Set G)) ∈ F.ZU.normalizerMonoidHom.ker := hh
      rwa [normalizerMonoidHom_ker] at hk
    have hz : r ∈ F.ZU := core_cubic_center_centralizer h structural alternatives F s hne x
      (F.Li_le L 1 hx).2 hx3 ▸ ⟨hr,hcz⟩
    exact hrL (pCoreIn_le 2 L (hZP hz))
  have hβ : β ≠ 1 := by
    intro hh
    have he := congrArg (fun a : MulAut F.ZU => e (a (e.symm (Multiplicative.ofAdd (1 : ZMod 4))))) hh
    change e ((e.symm (Multiplicative.ofAdd (1 : ZMod 4)))⁻¹) = e (e.symm (Multiplicative.ofAdd (1 : ZMod 4))) at he
    rw [map_inv,e.apply_symm_apply] at he
    have hh := congrArg Multiplicative.toAdd he
    exact (by decide : (-1 : ZMod 4) ≠ 1) hh
  have ha : Nat.card (MulAut F.ZU) = 2 := by
    rw [IsCyclic.card_mulAut, (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)]
    decide
  obtain ⟨a,_,hall⟩ := (Nat.card_eq_two_iff' (1 : MulAut F.ZU)).mp ha
  have he : α = β := (hall α hα).trans (hall β hβ).symm
  have hinv (z : G) (hz : z ∈ F.ZU) : r*z*r⁻¹ = z⁻¹ := by
    exact congrArg (fun a : MulAut F.ZU => (a ⟨z,hz⟩ : G)) he
  have hrT := point_core_le_sylow F hr.1
  have hrV := h.chosen.core_centralizes
    (core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 hr)
  intro p hp
  rw [← heP] at hp
  change p ∈ conjugateSpanBy F.ZU L at hp
  induction hp using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨l,hl,z,hz,rfl⟩ := ha
    have hq := seed_centralizer_displacement h structural r hrT hrV l hl
    have hp : l*z*l⁻¹ ∈ L.pCoreIn 2 :=
      (mem_normalizer_iff.mp ((L.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) hl) _).mp (hZP hz)
    have hrl : r*l*r⁻¹ = ⁅r,l⁆*l := by simp only [commutatorElement_def]; group
    calc
      r*(l*z*l⁻¹)*r⁻¹ = (r*l*r⁻¹)*(r*z*r⁻¹)*(r*l*r⁻¹)⁻¹ := by group
      _ = (⁅r,l⁆*l)*z⁻¹*(⁅r,l⁆*l)⁻¹ := by rw [hrl,hinv z hz]
      _ = ⁅r,l⁆*(l*z*l⁻¹)⁻¹*⁅r,l⁆⁻¹ := by group
      _ = (l*z*l⁻¹)⁻¹ := by rw [(hcomm _ _ hq ((L.pCoreIn 2).inv_mem hp)).eq,mul_inv_cancel_right]
  | one => simp
  | mul a b ha hb ha' hb' =>
    have hab := hcomm a b (heP ▸ ha) (heP ▸ hb)
    calc
      r*(a*b)*r⁻¹ = (r*a*r⁻¹)*(r*b*r⁻¹) := by group
      _ = a⁻¹*b⁻¹ := by rw [ha',hb']
      _ = (a*b)⁻¹ := by rw [mul_inv_rev,hab.inv_inv.eq]
  | inv a ha ha' =>
    calc
      r*a⁻¹*r⁻¹ = (r*a*r⁻¹)⁻¹ := by group
      _ = (a⁻¹)⁻¹ := by rw [ha']

/-- The outer involution's centralizer supplements P in the actual L, with
intersection exactly V. This is the original Frattini conclusion. -/
theorem outer_involution_actor_factorization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V) :
    L = L.pCoreIn 2 ⊔ (L ⊓ centralizer ({r} : Set G)) ∧
      L.pCoreIn 2 ⊓ centralizer ({r} : Set G) = V := by
  have heP := centerSpan_eq_core h structural alternatives F s hne
  have hVP := (seed_le_centerSpan h F).trans heP.le
  have hinv := outer_cubic_inverts_core h structural alternatives F s hne x hx hx3 r hr hrL
  have hrV := h.chosen.core_centralizes
    (core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 hr)
  constructor
  · apply le_antisymm ?_ (sup_le (pCoreIn_le 2 L) inf_le_left)
    intro l hl
    obtain ⟨p,hp,hp2⟩ := seed_exists_centerSpan_square h F s (hdis l hl)
    have hpP := heP ▸ hp
    have hpl : p*l ∈ centralizer ({r} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have he : r*(p*l)*r⁻¹ = p*l := by
        calc
          r*(p*l)*r⁻¹ = (r*p*r⁻¹)*(r*l*r⁻¹) := by group
          _ = p⁻¹*(r*l*r⁻¹) := by rw [hinv p hpP]
          _ = p⁻¹*⁅r,l⁆*l := by simp only [commutatorElement_def]; group
          _ = p*l := by rw [←hp2]; group
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hh := (L.pCoreIn 2 ⊔ (L ⊓ centralizer ({r} : Set G))).mul_mem
      (mem_sup_left ((L.pCoreIn 2).inv_mem hpP))
      (mem_sup_right ⟨L.mul_mem (pCoreIn_le 2 L hpP) hl,hpl⟩)
    simpa only [inv_mul_cancel_left] using hh
  · apply le_antisymm ?_ (le_inf hVP (by
      intro v hv
      exact mem_centralizer_singleton_iff.mpr (hrV v hv)))
    rintro p ⟨hp,hpr⟩
    have he : p⁻¹ = p := by
      rw [←hinv p hp,←mem_centralizer_singleton_iff.mp hpr,mul_inv_cancel_right]
    exact (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 p
      (heP.symm ▸ hp) |>.mp (by rw [pow_two]; simpa only [he] using inv_mul_cancel p)

/-- The original inner Sylow T∩L has index two in the order-eight branch. -/
theorem inner_sylow_index_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8) :
    (L.subgroupOf (T : Subgroup G)).index = 2 := by
  have hQ : Nat.card (F.H.pCoreIn 2) = 128 := by
    rw [point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives F s hne x hx hx3,hcard]
  have hT := sylow_card_of_point_core_card F s hQ
  have hI : Nat.card (L.subgroupOf (T : Subgroup G)) = 512 := by
    have he : L.subgroupOf (T : Subgroup G) = (L ⊓ (T : Subgroup G)).subgroupOf (T : Subgroup G) := by
      ext a
      exact ⟨fun ha => ⟨ha,a.property⟩,fun ha => ha.1⟩
    rw [he,Nat.card_congr (subgroupOfEquivOfLe (show L ⊓ (T : Subgroup G) ≤ (T : Subgroup G) from inf_le_right)).toEquiv]
    rw [inf_comm]
    exact sylow_inter_actor_card h structural alternatives F s hne
  have hh := (L.subgroupOf (T : Subgroup G)).card_mul_index
  rw [hI,hT] at hh
  omega

/-- The original quotient C_L(r)/V is L/P through literal inclusion and
quotient maps. In particular the natural action marking is preserved. -/
theorem outer_involution_actor_centralizer_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V) :
    ∃ hn : (V.subgroupOf (L ⊓ centralizer ({r} : Set G))).Normal,
      letI := hn
      ∃ e : ((L ⊓ centralizer ({r} : Set G) : Subgroup G) ⧸
          V.subgroupOf (L ⊓ centralizer ({r} : Set G))) ≃* (L ⧸ pCore 2 L),
        ∀ a : (L ⊓ centralizer ({r} : Set G) : Subgroup G),
          e (QuotientGroup.mk' (V.subgroupOf (L ⊓ centralizer ({r} : Set G))) a) =
            QuotientGroup.mk' (pCore 2 L) ⟨a,a.property.1⟩ := by
  let C := L ⊓ centralizer ({r} : Set G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let f : C →* (L ⧸ pCore 2 L) := q.comp (inclusion (show C ≤ L from inf_le_left))
  obtain ⟨hL,hI⟩ := outer_involution_actor_factorization h structural alternatives F s hne x hx hx3 r hr hrL hdis
  have hker : f.ker = V.subgroupOf C := by
    ext a
    have haL : (a:G) ∈ L := a.property.1
    have haC : (a:G) ∈ centralizer ({r} : Set G) := a.property.2
    change q (⟨a,haL⟩ : L) = 1 ↔ (a:G) ∈ V
    have hq : q (⟨a,haL⟩ : L) = 1 ↔ (⟨a,haL⟩ : L) ∈ pCore 2 L :=
      QuotientGroup.eq_one_iff _
    rw [hq]
    have he : (⟨a,haL⟩ : L) ∈ pCore 2 L ↔ (a:G) ∈ L.pCoreIn 2 := by
      constructor
      · exact fun ha => mem_map_of_mem L.subtype ha
      · rintro ⟨b,hb,he⟩
        exact (Subtype.ext he : b = ⟨a,haL⟩) ▸ hb
    rw [he,←hI]
    exact ⟨fun ha => ⟨ha,haC⟩,fun ha => ha.1⟩
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) a
    have hl : (l:G) ∈ (L.pCoreIn 2 : Set G) * (C : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (L.pCoreIn 2) C
        (inf_le_left.trans (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))),←hL]
      exact l.property
    obtain ⟨p,hp,c,hc,he⟩ := hl
    let pL : L := ⟨p,pCoreIn_le 2 L hp⟩
    let cL : L := ⟨c,hc.1⟩
    have heL : pL*cL = l := Subtype.ext he
    have hpq : q pL = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      obtain ⟨b,hb,he⟩ := hp
      exact (Subtype.ext he : b = pL) ▸ hb
    refine ⟨⟨c,hc⟩,?_⟩
    change q cL = q l
    rw [←heL,map_mul,hpq,one_mul]
  let hn : (V.subgroupOf C).Normal := hker ▸ f.normal_ker
  let := hn
  refine ⟨hn,(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf),?_⟩
  intro a
  change (QuotientGroup.quotientKerEquivOfSurjective f hf)
    (QuotientGroup.quotientMulEquivOfEq hker.symm
      (QuotientGroup.mk' (V.subgroupOf C) a)) = _
  rw [QuotientGroup.mk'_apply,QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The original centralizer C_L(r) has order 8·168. -/
theorem outer_involution_actor_centralizer_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V) :
    Nat.card (L ⊓ centralizer ({r} : Set G) : Subgroup G) = 1344 := by
  let := h.chosen.elementary
  obtain ⟨hn,e,_⟩ := outer_involution_actor_centralizer_quotient h structural alternatives F s hne x hx hx3 r hr hrL hdis
  let := hn
  let C := L ⊓ centralizer ({r} : Set G)
  have hrV := h.chosen.core_centralizes
    (core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 hr)
  have hVC : V ≤ C := le_inf h.chosen.le_component (fun v hv =>
    mem_centralizer_singleton_iff.mpr (hrV v hv))
  have hv : Nat.card (V.subgroupOf C) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv]
    simpa [F.last] using F.card 3 (by decide)
  have hq : Nat.card (C ⧸ V.subgroupOf C) = 168 :=
    (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr (h.naturalMarking.quotientEquiv.trans
        (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).toEquiv).trans Matrix.PSL3Two.card_SL)
  have hh := (V.subgroupOf C).card_mul_index
  rw [hv,index_eq_card,hq] at hh
  exact hh.symm

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
