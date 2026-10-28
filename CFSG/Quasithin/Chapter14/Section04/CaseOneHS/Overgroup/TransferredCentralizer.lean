module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterClosureFusion
public import Theory.Representation.SL2FourNaturalOrbits.FixedBound
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Action
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Geometry

/-!
# Centralizers of the transferred involution on the original closure

The component-core identification gives Q intersect PU=U. Thus an element
of PU outside U acts nontrivially on the literal U/Z(U). Its four-element
fixed subgroup is precisely the image of V, so its centralizer in U is
Z(U) times its centralizer in V. Outside P that latter subgroup is proper,
giving |C_U(y)| at most eight and |T:C_T(y)| at least eight.

The cyclic Z(U) lies in C_T(y); its squares are V₁. Hence V₁ lies in
the central Frattini subgroup of C_T(y), with the original embeddings.
These are the centralizer estimates used after the actual transfer placement.
Source: Aschbacher--Smith, 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The marked nontrivial action on the literal hatted module fixes at most four elements. -/
theorem point_hat_fixed_card_le_four
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (y : F.H) (hy : y ∉ pCore 2 F.H) :
    Nat.card (F.uhatAction y).fixedSubgroup ≤ 4 := by
  obtain ⟨e,c,he⟩ := s.natural
  let a := e (QuotientGroup.mk' (pCore 2 F.H) y)
  have ha : a.val ≠ 1 := by
    intro ha
    have heq : a = 1 := Subtype.ext ha
    exact hy ((QuotientGroup.eq_one_iff y).mp (e.injective (heq.trans e.map_one.symm)))
  have hn : a.val ∈ Representation.SL2FourNatural.SemilinearNormalizer.normalizer := by
    have hle : Representation.SL2FourNatural.SemilinearNormalizer.specialField ≤
        Representation.SL2FourNatural.SemilinearNormalizer.normalizer := by
      rw [←Representation.SL2FourNatural.SemilinearNormalizer.semilinear_eq_normalizer,
        ←Representation.SL2FourNatural.SemilinearNormalizer.specialFieldGamma_map_natural]
      exact Subgroup.map_le_range _ _
    exact hle a.property
  let f : (F.uhatAction y).fixedSubgroup → a.val.toLinearMap.fixedSubmodule := fun v =>
    ⟨(c v).toAdd, by
      change a.val (c v).toAdd = (c v).toAdd
      rw [←he]
      exact congrArg (fun w => (c w).toAdd) ((MulAut.mem_fixedSubgroup _ _).mp v.property)⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply c.injective
    apply Multiplicative.toAdd.injective
    exact congrArg Subtype.val huv
  exact (Nat.card_le_card_of_injective f hf).trans
    (Representation.SL2FourNatural.normalizer_nonidentity_fixed_card_le_four a.val hn ha)

/-- The original point core intersects PU in exactly U. -/
theorem core_closure_inter_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    (L.pCoreIn 2 ⊔ F.U) ⊓ F.H.pCoreIn 2 = F.U := by
  obtain ⟨K,hKH,hK,hKT,hU,_⟩ := s.component
  have hPK := core_closure_le_component h structural alternatives F s hne K hKH hK hKT hU
  have he := component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU
  apply le_antisymm ?_ (le_inf le_sup_right (by
    let := h.chosen.elementary
    exact le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 6) s.core_shape.card)
      F.U_le_H (le_normalizer_conjugateSpanBy V F.H)))
  exact ((inf_le_inf_right _ hPK).trans (inf_pCoreIn_le_of_le 2 hKH)).trans he.ge

/-- All displacements of PU on V lie in the original point V₁. -/
theorem core_closure_seed_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) (v : G) (hv : v ∈ V) :
    ⁅y,v⁆ ∈ F.Vi 1 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let := centerSpan_abelian h structural F s
  have heP := centerSpan_eq_core h structural alternatives F s hne
  have hVP := (seed_le_centerSpan h F).trans heP.le
  have hcomm (p z : G) (hp : p ∈ L.pCoreIn 2) (hz : z ∈ V) : Commute p z :=
    congrArg Subtype.val (mul_comm (⟨p,heP.symm ▸ hp⟩ : centerSpan L F)
      ⟨z,heP.symm ▸ hVP hz⟩)
  have hn : F.U ≤ normalizer (L.pCoreIn 2 : Set G) :=
    (closure_le_actor h structural alternatives F s hne).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hyprod : y ∈ (L.pCoreIn 2 : Set G) * (F.U : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hy
  obtain ⟨p,hp,u,hu,rfl⟩ := hyprod
  let : Fact (IsPGroup 2 F.U) := ⟨IsPGroup.of_card (n:=6) s.core_shape.card⟩
  have hdu : ⁅(⟨u,hu⟩ : F.U),⟨v,le_conjugateSpanBy V F.H hv⟩⁆ ∈ frattini F.U :=
    commutator_le_frattini_of_isPGroup (p:=2)
      (Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
  have hd : ⁅u,v⁆ ∈ F.Vi 1 := (closure_frattini h structural alternatives F hne) ▸
    mem_map_of_mem F.U.subtype hdu
  have he : ⁅p*u,v⁆ = ⁅u,v⁆ := by
    calc
      ⁅p*u,v⁆ = p*⁅u,v⁆*p⁻¹ := by
        calc
          ⁅p*u,v⁆ = p*(u*v*u⁻¹)*(p⁻¹*v⁻¹) := by
            simp only [commutatorElement_def]
            group
          _ = p*(u*v*u⁻¹)*(v⁻¹*p⁻¹) := by rw [(hcomm p v hp hv).inv_inv.eq]
          _ = p*⁅u,v⁆*p⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅u,v⁆ := by rw [(hcomm p _ hp (F.le_seed 1 hd)).eq,mul_inv_cancel_right]
  exact he ▸ hd

/-- An element of PU outside U fixes precisely the original hatted seed. -/
theorem core_closure_nonclosure_hat_fixed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : F.H) (hy : (y:G) ∈ L.pCoreIn 2 ⊔ F.U) (hyU : (y:G) ∉ F.U) :
    (F.uhatAction y).fixedSubgroup = hatImage F V := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hfix : hatImage F V ≤ (F.uhatAction y).fixedSubgroup := by
    rintro q ⟨v,hv,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [F.uhatAction_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hz : ⁅(y:G),(v:G)⁆ ∈ F.ZU := F.point_le_ZU (by decide)
      (core_closure_seed_displacement h structural alternatives F s hne y hy v hv)
    obtain ⟨b,hb,he⟩ := hz
    have heb : b = F.uAction y v / v := by
      apply Subtype.ext
      change F.U.subtype b = ((y:G)*(v:G)*(y:G)⁻¹)/(v:G)
      simpa only [commutatorElement_def,div_eq_mul_inv] using he
    exact heb ▸ hb
  have hyQ : y ∉ pCore 2 F.H := by
    intro hyQ
    exact hyU (core_closure_inter_point_core h structural alternatives F s hne ▸
      ⟨hy,mem_map_of_mem F.H.subtype hyQ⟩)
  have hc := card_hatImage_mul_card_inf F V (le_conjugateSpanBy V F.H)
  rw [F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne] at hc
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [hp,hv] at hc
  exact (eq_of_le_of_card_ge hfix (by
    have hh := point_hat_fixed_card_le_four F s y hyQ
    omega)).symm

/-- The original U-centralizer is Z(U) times the original V-centralizer. -/
theorem core_closure_nonclosure_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) (hyU : y ∉ F.U) :
    F.U ⊓ centralizer ({y} : Set G) =
      (V ⊓ centralizer ({y} : Set G)) ⊔ F.ZU := by
  let := h.chosen.elementary
  have hyH := (F.invariant 1) (core_closure_le_sylow h structural F s hy)
  have hZC : F.ZU ≤ centralizer ({y} : Set G) := by
    intro z hz
    apply mem_centralizer_singleton_iff.mpr
    have hzC : z ∈ centralizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G) :=
      ((sylow_core_closure_centralizer h structural alternatives F s hne).symm ▸ hz).2
    exact (hzC y hy).symm
  have hZU : F.ZU ≤ F.U := map_subtype_le _
  apply le_antisymm ?_ (sup_le (le_inf (inf_le_left.trans (le_conjugateSpanBy V F.H)) inf_le_right)
    (le_inf hZU hZC))
  rintro u ⟨hu,huy⟩
  have hhat : QuotientGroup.mk' (center F.U) ⟨u,hu⟩ ∈ hatImage F V := by
    rw [←core_closure_nonclosure_hat_fixed h structural alternatives F s hne ⟨y,hyH⟩ hy hyU]
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [F.uhatAction_apply_mk]
    congr 1
    apply Subtype.ext
    change y*u*y⁻¹=u
    rw [←mem_centralizer_singleton_iff.mp huy,mul_inv_cancel_right]
  have huVZ := (mem_hatImage_mk_iff F V (le_conjugateSpanBy V F.H) ⟨u,hu⟩).mp hhat
  have hn : F.ZU ≤ normalizer (V : Set G) :=
    ((centerIn_le_centralizer F.U).trans (centralizer_le (le_conjugateSpanBy V F.H))).trans
      (Subgroup.centralizer_le_normalizer _)
  have huprod : u ∈ (V : Set G) * (F.ZU : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
    exact huVZ
  obtain ⟨v,hv,z,hz,rfl⟩ := huprod
  have hvy : v ∈ centralizer ({y} : Set G) := by
    have hh := (centralizer ({y} : Set G)).mul_mem huy ((centralizer _).inv_mem (hZC hz))
    simpa only [mul_inv_cancel_right] using hh
  exact mul_mem_sup ⟨hv,hvy⟩ hz

/-- The entire actual PU centralizes the cyclic center of U. -/
theorem core_closure_centralizes_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    L.pCoreIn 2 ⊔ F.U ≤ centralizer (F.ZU : Set G) := by
  apply le_centralizer_iff.mp
  rw [←sylow_core_closure_centralizer h structural alternatives F s hne]
  exact inf_le_right

/-- Outside P the seed centralizer is proper and has at most four elements. -/
theorem core_closure_noncore_seed_centralizer_card_le_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) (hyP : y ∉ L.pCoreIn 2) :
    Nat.card (V ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 4 := by
  let D := V ⊓ centralizer ({y} : Set G)
  have hDV : D ≤ V := inf_le_left
  have hproper : D.subgroupOf V ≠ ⊤ := by
    intro he
    have hyV : y ∈ centralizer (V : Set G) := by
      intro v hv
      have hd : (⟨v,hv⟩ : V) ∈ D.subgroupOf V := he ▸ mem_top _
      exact mem_centralizer_singleton_iff.mp hd.2
    have hyL := (sup_le (pCoreIn_le 2 L) (closure_le_actor h structural alternatives F s hne)) hy
    exact hyP (h.centralizer_L ▸ ⟨hyL,hyV⟩)
  have hi : 2 ≤ (D.subgroupOf V).index := by
    have hn := index_ne_zero_of_finite (H := D.subgroupOf V)
    have hh : (D.subgroupOf V).index ≠ 1 := fun he => hproper (index_eq_one.mp he)
    omega
  have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hh := (D.subgroupOf V).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hDV).toEquiv,hc] at hh
  have hineq := Nat.mul_le_mul_left (Nat.card D) hi
  change Nat.card D ≤ 4
  omega

/-- An element of PU outside both P and U has U-centralizer of order at most eight. -/
theorem core_closure_nonclosure_centralizer_card_le_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) (hyP : y ∉ L.pCoreIn 2) (hyU : y ∉ F.U) :
    Nat.card (F.U ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 8 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let D := V ⊓ centralizer ({y} : Set G)
  have hZC : F.ZU ≤ centralizer ({y} : Set G) := fun z hz =>
    mem_centralizer_singleton_iff.mpr (core_closure_centralizes_center h structural alternatives F s hne hy z hz)
  have hi : D ⊓ F.ZU = F.Vi 1 := by
    rw [←F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne]
    ext a
    exact ⟨fun ha => ⟨ha.1.1,ha.2⟩,fun ha => ⟨⟨ha.1,hZC ha.2⟩,ha.2⟩⟩
  have hn : F.ZU ≤ normalizer (D : Set G) :=
    ((centerIn_le_centralizer F.U).trans (centralizer_le
      (inf_le_left.trans (le_conjugateSpanBy V F.H)))).trans (Subgroup.centralizer_le_normalizer _)
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes D F.ZU hn
  obtain ⟨e⟩ := center_model F s
  have hz : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  rw [hz,hi,hp,←core_closure_nonclosure_centralizer h structural alternatives F s hne y hy hyU] at hh
  have hd := core_closure_noncore_seed_centralizer_card_le_four h structural alternatives F s hne y hy hyP
  change Nat.card D ≤ 4 at hd
  omega

/-- The original U-orbit forces Sylow centralizer index at least eight. -/
theorem core_closure_nonclosure_sylow_centralizer_bound
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) (hyP : y ∉ L.pCoreIn 2) (hyU : y ∉ F.U) :
    8 * Nat.card ((T : Subgroup G) ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ Nat.card T := by
  let := h.chosen.elementary
  let C := (T : Subgroup G) ⊓ centralizer ({y} : Set G)
  have hn : C ≤ normalizer (F.U : Set G) :=
    inf_le_left.trans ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
  have hi : F.U ⊓ C = F.U ⊓ centralizer ({y} : Set G) := by
    ext a
    exact ⟨fun ha => ⟨ha.1,ha.2.2⟩,fun ha => ⟨ha.1,closure_le_sylow F s ha.1,ha.2⟩⟩
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.U C hn
  rw [s.core_shape.card,hi] at hh
  have hcu := core_closure_nonclosure_centralizer_card_le_eight h structural alternatives F s hne y hy hyP hyU
  have hj : Nat.card (F.U ⊔ C : Subgroup G) ≤ Nat.card T :=
    card_le_of_le (sup_le (closure_le_sylow F s) inf_le_left)
  have hineq := Nat.mul_le_mul hcu hj
  rw [←hh] at hineq
  change 8 * Nat.card C ≤ Nat.card T
  omega

/-- The original point lies in the central Frattini subgroup of the transferred centralizer. -/
theorem core_closure_point_le_central_frattini
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (y : G) (hy : y ∈ L.pCoreIn 2 ⊔ F.U) :
    let C := (T : Subgroup G) ⊓ centralizer ({y} : Set G)
    F.Vi 1 ≤ Chapter12.Section08.centerIn C ⊓ (frattini C).map C.subtype := by
  let := h.chosen.elementary
  let C := (T : Subgroup G) ⊓ centralizer ({y} : Set G)
  let : Fact (IsPGroup 2 C) := ⟨T.isPGroup'.of_injective (inclusion (show C ≤ (T : Subgroup G) from inf_le_left))
    (inclusion_injective _)⟩
  have hZC : F.ZU ≤ C := le_inf
    ((map_subtype_le (center F.U)).trans (closure_le_sylow F s))
    (fun z hz => mem_centralizer_singleton_iff.mpr
      (core_closure_centralizes_center h structural alternatives F s hne hy z hz))
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hpointC : F.Vi 1 ≤ Chapter12.Section08.centerIn C := by
    rw [centerIn_eq_inf_centralizer]
    refine le_inf ((F.point_le_ZU (by decide)).trans hZC) ?_
    intro z hz c hc
    exact (normalizer_le_centralizer_of_card_two _ hp (F.invariant 1 hc.1) z hz).symm
  change F.Vi 1 ≤ Chapter12.Section08.centerIn C ⊓ (frattini C).map C.subtype
  refine le_inf hpointC ?_
  intro z hz
  have hsq : z ∈ (centralSquares F.U).map F.U.subtype := (center_squares_eq_point h F s).symm ▸ hz
  obtain ⟨v,hv,rfl⟩ := hsq
  obtain ⟨w,hw⟩ := mem_centralSquares.mp hv
  have hwC : (w.val:G) ∈ C := hZC (mem_map_of_mem F.U.subtype w.property)
  refine ⟨(⟨w.val,hwC⟩ : C)^2,pth_power_mem_frattini_of_isPGroup (p:=2) _,?_⟩
  exact congrArg Subtype.val hw

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
