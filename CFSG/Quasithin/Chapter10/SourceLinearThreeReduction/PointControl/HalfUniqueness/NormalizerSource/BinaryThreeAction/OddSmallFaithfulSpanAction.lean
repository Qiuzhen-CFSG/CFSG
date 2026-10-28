module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallModuleSpanAction

/-!
# The original action restricted to its module-core span

The invariant subgroup is the span of the actual image of V intersect O₂(K).
All action formulas below use the original Frattini section and its original
quotient action. The nontrivial-image branch is kept explicit.
Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

private def restrictSpanAction {B W : Type*} [Group B] [Group W]
    (b : B →* MulAut W) (M : Subgroup W)
    (hinv : ∀ x, M.map (b x).toMonoidHom = M) : B →* MulAut M where
  toFun x := ((b x).subgroupMap M).trans (MulEquiv.subgroupCongr (hinv x))
  map_one' := by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact DFunLike.congr_fun b.map_one (w : W)
  map_mul' x y := by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact DFunLike.congr_fun (b.map_mul x y) (w : W)

private theorem faithful_span_restriction {B W A : Type*}
    [Group B] [Finite B] [Group A] [CommGroup W] [IsElementaryAbelian 2 W]
    [Group.IsPerfect B] (b : B →* MulAut W) (hb : Function.Injective b)
    (hcore : pCore 2 B = ⊥) (M : Subgroup W)
    (hinv : ∀ x, M.map (b x).toMonoidHom = M)
    (α : A →* MulAut W) (κ : A →* B)
    (hgen : normalClosure (κ.range : Set B) = ⊤)
    (hdisp : ∀ a w, w⁻¹ * α a w ∈ M)
    (hmark : ∀ a x, b (κ a*x*(κ a)⁻¹) = α a*b x*(α a)⁻¹) :
    (∀ x w, w⁻¹ * b x w ∈ M) ∧ Function.Injective (restrictSpanAction b M hinv) := by
  let _ : MulDistribMulAction B W := MulDistribMulAction.compHom W b
  have hM : IsInvariant B W M := by
    constructor
    intro x w
    constructor
    · intro hw
      exact hinv x ▸ mem_map_of_mem (b x).toMonoidHom hw
    · intro hw
      have hh := hinv x⁻¹ ▸ mem_map_of_mem (b x⁻¹).toMonoidHom hw
      change b x⁻¹ (b x w) ∈ M at hh
      simpa only [map_inv,MulAut.inv_apply_self] using hh
  let _ : MulDistribMulAction B (W ⧸ M) := quotientMulDistribMulAction M hM
  let ν : B →* MulAut (W ⧸ M) := MulDistribMulAction.toMulAut B (W ⧸ M)
  let q := QuotientGroup.mk' M
  have hν (x) (w) : ν x (q w) = q (b x w) := rfl
  have hα (a) (w) : q (α a w) = q w := by
    symm
    apply (inv_mul_eq_one.mp)
    rw [←map_inv,←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hdisp a w)
  have hαinv (a) (w) : q ((α a)⁻¹ w) = q w := by
    rw [←map_inv]
    exact hα a⁻¹ w
  have hcentral : κ.range ≤ (center ν.range).comap ν.rangeRestrict := by
    rintro _ ⟨a,rfl⟩
    change ν.rangeRestrict (κ a) ∈ center ν.range
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,hy⟩ := x.property
    apply Subtype.ext
    change (x : MulAut (W ⧸ M)) * ν (κ a) = ν (κ a) * (x : MulAut (W ⧸ M))
    rw [←hy]
    have he : ν (κ a*y*(κ a)⁻¹) = ν y := by
      apply MulEquiv.ext
      intro z
      obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective M z
      rw [hν,hmark]
      change q (α a (b y ((α a)⁻¹ w))) = q (b y w)
      rw [hα,←hν,hαinv,hν]
    have hh : ν (κ a)*ν y*(ν (κ a))⁻¹ = ν y := by
      simpa only [map_mul,map_inv] using he
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hz : (center ν.range).comap ν.rangeRestrict = ⊤ :=
    top_unique (hgen ▸ normalClosure_le_normal hcentral)
  let : IsMulCommutative ν.range := center_eq_top_iff.mp (by
    apply top_unique
    intro x _
    obtain ⟨y,rfl⟩ := ν.rangeRestrict_surjective x
    have hh : y ∈ (center ν.range).comap ν.rangeRestrict := hz ▸ mem_top y
    exact hh)
  let : Group.IsPerfect ν.range := Group.IsPerfect.range ν
  have hv (x) : ν x = 1 := congrArg Subtype.val
    (Subsingleton.elim (ν.rangeRestrict x) (1 : ν.range))
  have hd (x) (w) : w⁻¹ * b x w ∈ M := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (w⁻¹*b x w) = 1
    rw [map_mul,map_inv,←hν,hv,MulAut.one_apply,inv_mul_cancel]
  refine ⟨hd,?_⟩
  let β := restrictSpanAction b M hinv
  have htwo : IsPGroup 2 β.ker := by
    intro x
    refine ⟨1,?_⟩
    apply Subtype.ext
    change (x:B)^2=1
    apply hb
    apply MulEquiv.ext
    intro w
    have hh := congrArg (fun t : MulAut M => (t ⟨w⁻¹*b x w,hd x w⟩ : W))
      (show β x=1 from x.property)
    change b x (w⁻¹*b x w) = w⁻¹*b x w at hh
    have hpow (v:W) : v^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) v
    have hinvW (v:W) : v⁻¹=v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow v)
    simp only [map_mul,hinvW] at hh
    have hxx : b x (b x w) = w := mul_left_cancel (hh.trans (mul_comm _ _))
    simpa only [pow_two,map_mul,map_one,MulAut.mul_apply,MulAut.one_apply] using hxx
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  rw [←hcore]
  exact le_sSup ⟨inferInstance,htwo⟩

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P I : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

private theorem normalClosure_prod_nontrivial {J : Type*} [Group J] [IsSimpleGroup J]
    (C D : Subgroup J) (hc : C ≠ ⊥) (hd : D ≠ ⊥) :
    normalClosure (C.prod D : Set (J × J)) = ⊤ := by
  let N := normalClosure (C.prod D : Set (J × J))
  have hl : N.comap (MonoidHom.inl J J) = ⊤ := by
    apply (inferInstance : (N.comap (MonoidHom.inl J J)).Normal).eq_bot_or_eq_top.resolve_left
    intro hz
    apply hc
    apply bot_unique
    intro c hcm
    have hh : c ∈ N.comap (MonoidHom.inl J J) := subset_normalClosure ⟨hcm,D.one_mem⟩
    rwa [hz] at hh
  have hr : N.comap (MonoidHom.inr J J) = ⊤ := by
    apply (inferInstance : (N.comap (MonoidHom.inr J J)).Normal).eq_bot_or_eq_top.resolve_left
    intro hz
    apply hd
    apply bot_unique
    intro d hdm
    have hh : d ∈ N.comap (MonoidHom.inr J J) := subset_normalClosure ⟨C.one_mem,hdm⟩
    rwa [hz] at hh
  apply top_unique
  rintro ⟨x,y⟩ _
  have hx : (x,1) ∈ N := by
    change x ∈ N.comap (MonoidHom.inl J J)
    rw [hl]; exact mem_top _
  have hy : (1,y) ∈ N := by
    change y ∈ N.comap (MonoidHom.inr J J)
    rw [hr]; exact mem_top _
  simpa only [Prod.mk_mul_mk,mul_one,one_mul] using N.mul_mem hx hy

private theorem pair_cubic_centralizer_generates {F : Type} [Field F] [Finite F]
    [IsSimpleGroup PSL(2,F)]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : ¬ 8 ∣ Nat.card PSL(2,F)) (S : Sylow 2 (PSL(2,F) × PSL(2,F)))
    (P : Subgroup (PSL(2,F) × PSL(2,F))) [IsElementaryAbelian 3 P]
    [IsCyclic (P.map (MonoidHom.fst _ _))] [IsCyclic (P.map (MonoidHom.snd _ _))]
    (hP : Nat.card P = 9) (hn : (S : Subgroup (PSL(2,F) × PSL(2,F))) ≤
      normalizer (P : Set (PSL(2,F) × PSL(2,F)))) :
    normalClosure (↑((S : Subgroup (PSL(2,F) × PSL(2,F))) ⊓
      centralizer (P : Set (PSL(2,F) × PSL(2,F)))) :
      Set (PSL(2,F) × PSL(2,F))) = ⊤ := by
  let V := S.mapSurjective (f := MonoidHom.fst _ _) (fun x => ⟨(x,1),rfl⟩)
  let W := S.mapSurjective (f := MonoidHom.snd _ _) (fun x => ⟨(1,x),rfl⟩)
  let := Theory.PSL2.small_sylow_kleinFour hF h8 V
  let := Theory.PSL2.small_sylow_kleinFour hF h8 W
  have hprod : (S : Subgroup (PSL(2,F) × PSL(2,F))) =
      (V : Subgroup PSL(2,F)).prod (W : Subgroup PSL(2,F)) := by
    symm
    apply S.is_maximal'
    · apply IsPGroup.of_card (n := 4)
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,
        IsKleinFour.card_four,IsKleinFour.card_four]
      norm_num
    · intro x hx
      exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩
  let C := P.map (MonoidHom.fst _ _)
  let D := P.map (MonoidHom.snd _ _)
  have hVC : (V : Subgroup PSL(2,F)) ≤ normalizer (C : Set PSL(2,F)) := by
    intro x hx
    exact le_normalizer_map (MonoidHom.fst _ _) (mem_map_of_mem _
      (hn (hprod.symm ▸ (show (x,1) ∈ (V : Subgroup PSL(2,F)).prod (W : Subgroup PSL(2,F)) from ⟨hx,one_mem _⟩))))
  have hWD : (W : Subgroup PSL(2,F)) ≤ normalizer (D : Set PSL(2,F)) := by
    intro x hx
    exact le_normalizer_map (MonoidHom.snd _ _) (mem_map_of_mem _
      (hn (hprod.symm ▸ (show (1,x) ∈ (V : Subgroup PSL(2,F)).prod (W : Subgroup PSL(2,F)) from ⟨one_mem _,hx⟩))))
  have he : (S : Subgroup (PSL(2,F) × PSL(2,F))) ⊓ centralizer (P : Set (PSL(2,F) × PSL(2,F))) =
      ((V : Subgroup PSL(2,F)) ⊓ centralizer (C : Set PSL(2,F))).prod
        ((W : Subgroup PSL(2,F)) ⊓ centralizer (D : Set PSL(2,F))) := by
    rw [hprod]
    ext x
    constructor
    · intro hx
      refine ⟨⟨hx.1.1,?_⟩,⟨hx.1.2,?_⟩⟩
      · rintro y ⟨z,hz,rfl⟩; exact congrArg Prod.fst (hx.2 z hz)
      · rintro y ⟨z,hz,rfl⟩; exact congrArg Prod.snd (hx.2 z hz)
    · intro hx
      exact ⟨⟨hx.1.1,hx.2.1⟩,fun z hz =>
        Prod.ext (hx.1.2 _ (mem_map_of_mem _ hz)) (hx.2.2 _ (mem_map_of_mem _ hz))⟩
  rw [he]
  obtain ⟨hc,hd⟩ := cubic_plane_projection_cards P hP
  apply normalClosure_prod_nontrivial
  · have hh := four_cubic_kernel_card (V : Subgroup PSL(2,F)) C
      (GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF V inferInstance) hc hVC
    intro hz
    rw [hz,card_bot] at hh
    norm_num at hh
  · have hh := four_cubic_kernel_card (W : Subgroup PSL(2,F)) D
      (GorensteinWalter.psl2_kleinFour_centralizer_eq_self F hF W inferInstance) hd hWD
    intro hz
    rw [hz,card_bot] at hh
    norm_num at hh

private theorem Data.cubic_sylow_centralizer_generates (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    normalClosure (↑(quotientImage (enlargedResidual T L H) (T : Subgroup G) ⊓
      centralizer (quotientImage (enlargedResidual T L H) P : Set _)) :
        Set (XiQuotient (enlargedResidual T L H))) = ⊤ := by
  let K := enlargedResidual T L H
  let C := quotientImage K P
  obtain ⟨S,hS⟩ := h.quotient_sylow
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  let : IsElementaryAbelian 3 P := hpc.1
  let : IsElementaryAbelian 3 (P.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf (hs.toLocalInput.complement_le.trans h.residual_le_enlargedResidual)
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 K))
  have hep : Nonempty (P ≃* quotientImage K P) := by
    rw [show K = componentOrbit I (T : Subgroup G) from hK]
    exact ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hC : Nat.card C = 9 := (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  let : IsSimpleGroup (XiQuotient I) :=
    SwappedFactorsProof.quotient_simple hs.toSwappedInput (.linear_prime p hp ho hm)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : IsSimpleGroup PSL(2,F) := eF.symm.isSimpleGroup
  let j := e.trans (eF.prodCongr eF)
  have hr : primeRank 3 (PSL(2,F) × PSL(2,F)) ≤ 2 := by
    rw [←primeRank_congr 3 j,hK]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3
      (by decide) (by decide)
  let C' := C.map j.toMonoidHom
  let : IsElementaryAbelian 3 C' := IsElementaryAbelian.map j.toMonoidHom
  have hthree : IsPGroup 3 C' := IsElementaryAbelian.isPGroup 3 C'
  let : IsCyclic (C'.map (MonoidHom.fst PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  let : IsCyclic (C'.map (MonoidHom.snd PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  have hN : (S : Subgroup (XiQuotient K)) ≤ normalizer (C : Set _) := by
    rw [hS,show C = quotientImage K (residual H) from
      (h.quotient_residual_eq_complement_of_core_le hs.toLocalInput hc).symm]
    apply (map_mono ?_).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 K)))
    rw [←subgroupOf_normalizer_eq h.residual_le_enlargedResidual]
    exact subgroupOf_mono K hs.invariant
  have h8 : p % 8 = 3 ∨ p % 8 = 5 := by omega
  have hgen := pair_cubic_centralizer_generates
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
    (Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ h8))
    (S.mapSurjective (f := j.toMonoidHom) j.surjective) C'
    (by rw [card_map_of_injective j.injective]; exact hC)
    ((map_mono hN).trans (le_normalizer_map j.toMonoidHom))
  rw [←hS]
  apply (map_injective (f := j.toMonoidHom) j.injective)
  rw [map_top_of_surjective _ j.surjective,map_normalClosure _ _ j.surjective]
  change normalClosure (↑((S : Subgroup _).map j.toMonoidHom ⊓
    centralizer (C' : Set _)) : Set (PSL(2,F) × PSL(2,F))) = ⊤ at hgen
  have he : ((S : Subgroup _) ⊓ centralizer (C : Set _)).map j.toMonoidHom =
      (S : Subgroup _).map j.toMonoidHom ⊓ centralizer (C' : Set _) := by
    rw [map_inf _ _ _ j.injective,Theory.GroupTheory.map_centralizer_equiv]
    rfl
  rw [←he] at hgen
  exact hgen

/-- The original containing quotient acts on the actual module-core span. -/
def Data.coreSpanQuotientAction (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    XiQuotient (enlargedResidual T L H) →* MulAut (h.moduleCoreSpan hn) :=
  restrictSpanAction (h.coreQuotientFrattiniAction hn) (h.moduleCoreSpan hn)
    (h.moduleCoreSpan_invariant hn)

/-- Restriction retains the literal action on each element of the span. -/
theorem Data.coreSpanQuotientAction_apply (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (x : XiQuotient (enlargedResidual T L H)) (w : h.moduleCoreSpan hn) :
    (h.coreSpanQuotientAction hn x w : CoreFrattiniSection T L H) =
      h.coreQuotientFrattiniAction hn x w := by rfl

/-- Original module displacements lie in the actual invariant span. -/
theorem Data.module_displacement_mem_coreSpan (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (a : moduleFrattiniImage D H) (w : CoreFrattiniSection T L H) :
    w⁻¹ * (a : MulAut (CoreFrattiniSection T L H)) w ∈ h.moduleCoreSpan hn :=
  h.moduleCoreImage_le_span hn (h.moduleFrattiniImage_displacement hfull
    (by rw [commutatorAction_eq_closure]; exact subset_closure ⟨a,w,rfl⟩))

private theorem Data.coreSpan_module_invariant (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (a : moduleFrattiniImage D H) :
    (h.moduleCoreSpan hn).map (a : MulAut (CoreFrattiniSection T L H)).toMonoidHom =
      h.moduleCoreSpan hn := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨w,hw,rfl⟩
    change (a : MulAut (CoreFrattiniSection T L H)) w ∈ h.moduleCoreSpan hn
    have hh := (h.moduleCoreSpan hn).mul_mem hw
      (h.module_displacement_mem_coreSpan hfull hn a w)
    simpa only [mul_inv_cancel_left] using hh
  · rw [card_map_of_injective (a : MulAut (CoreFrattiniSection T L H)).injective]

/-- Restriction of the unchanged original module action to its actual span. -/
def Data.coreSpanModuleAction (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    moduleFrattiniImage D H →* MulAut (h.moduleCoreSpan hn) :=
  restrictSpanAction (moduleFrattiniImage D H).subtype (h.moduleCoreSpan hn)
    (h.coreSpan_module_invariant hfull hn)

/-- The restricted original action has its original pointwise formula. -/
theorem Data.coreSpanModuleAction_apply (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (a : moduleFrattiniImage D H) (w : h.moduleCoreSpan hn) :
    (h.coreSpanModuleAction hfull hn a w : CoreFrattiniSection T L H) =
      (a : MulAut (CoreFrattiniSection T L H)) w := by rfl

/-- The same module action remains quadratic on its actual invariant span. -/
theorem Data.coreSpanModuleAction_quadratic (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let _ : MulDistribMulAction (moduleFrattiniImage D H) (h.moduleCoreSpan hn) :=
      MulDistribMulAction.compHom _ (h.coreSpanModuleAction hfull hn)
    commutatorAction₂ (moduleFrattiniImage D H) (h.moduleCoreSpan hn) = ⊥ := by
  let _ : MulDistribMulAction (moduleFrattiniImage D H) (h.moduleCoreSpan hn) :=
    MulDistribMulAction.compHom _ (h.coreSpanModuleAction hfull hn)
  have hd : commutatorAction (moduleFrattiniImage D H) (h.moduleCoreSpan hn) ≤
      (moduleCoreImage D H).comap (h.moduleCoreSpan hn).subtype := by
    rw [commutatorAction_eq_closure,closure_le]
    rintro _ ⟨a,w,rfl⟩
    change (w : CoreFrattiniSection T L H)⁻¹ *
      (a : MulAut (CoreFrattiniSection T L H)) (w : CoreFrattiniSection T L H) ∈ moduleCoreImage D H
    exact h.moduleFrattiniImage_displacement hfull (by
      rw [commutatorAction_eq_closure]; exact subset_closure ⟨a,(w : CoreFrattiniSection T L H),rfl⟩)
  apply bot_unique
  apply (closure_le (K := (⊥ : Subgroup (h.moduleCoreSpan hn)))).mpr
  rintro _ ⟨a,w,hw,rfl⟩
  have hf := h.moduleFrattiniImage_fixes_module_image hfull (hd hw) a
  have he : a • w = w := Subtype.ext hf
  rw [he,inv_mul_cancel]
  exact one_mem _

/-- Restriction to the actual span inherits the fixed-index bound sixteen. -/
theorem Data.coreSpanModuleAction_fixed_index (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    let _ : MulDistribMulAction (moduleFrattiniImage D H) (h.moduleCoreSpan hn) :=
      MulDistribMulAction.compHom _ (h.coreSpanModuleAction s.full_eq_local hn)
    (FixedPoints.subgroup (moduleFrattiniImage D H) (h.moduleCoreSpan hn)).index ≤ 16 := by
  let _ : MulDistribMulAction (moduleFrattiniImage D H) (h.moduleCoreSpan hn) :=
    MulDistribMulAction.compHom _ (h.coreSpanModuleAction s.full_eq_local hn)
  change (FixedPoints.subgroup (moduleFrattiniImage D H) (h.moduleCoreSpan hn)).index ≤ 16
  have he : FixedPoints.subgroup (moduleFrattiniImage D H) (h.moduleCoreSpan hn) =
      (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).comap
        (h.moduleCoreSpan hn).subtype := by
    ext w
    constructor
    · intro hw a
      exact congrArg Subtype.val (hw a)
    · intro hw a
      exact Subtype.ext (hw a)
  rw [he,index_comap,range_subtype]
  exact (relIndex_le_of_le_right (show h.moduleCoreSpan hn ≤ ⊤ from le_top)
    (by simpa only [relIndex_top_right] using
      (index_ne_zero_of_finite (H := FixedPoints.subgroup (moduleFrattiniImage D H)
        (CoreFrattiniSection T L H))))).trans
    (by simpa only [relIndex_top_right] using
      Nat.le_of_dvd (by decide) (h.collapsed_moduleFrattiniImage_fixed_index f hi hP hc))

/-- The actual inner implementers form a faithful embedding. In the nontrivial
branch their image is exactly the original Sylow centralizer of the cubic. -/
theorem Data.exists_coreSpan_inner_embedding (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    ∃ κ : moduleFrattiniImage D H →* XiQuotient (enlargedResidual T L H),
      Function.Injective κ ∧
      κ.range = quotientImage (enlargedResidual T L H) (T : Subgroup G) ⊓
        centralizer (quotientImage (enlargedResidual T L H) P : Set _) ∧
      h.coreSpanModuleAction s.full_eq_local hn = (h.coreSpanQuotientAction hn).comp κ ∧
      ∀ a x, h.coreQuotientFrattiniAction hn (κ a * x * (κ a)⁻¹) =
        (a : MulAut (CoreFrattiniSection T L H)) * h.coreQuotientFrattiniAction hn x *
          (a : MulAut (CoreFrattiniSection T L H))⁻¹ := by
  let B := XiQuotient (enlargedResidual T L H)
  let b := h.coreQuotientFrattiniAction hn
  have hZ : center B = ⊥ := by
    obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
    obtain ⟨F,_,_,_,⟨eF⟩⟩ := hm
    have he := Nat.card_congr (centerCongr (e.trans (eF.prodCongr eF))).toEquiv
    apply card_eq_one.mp
    rw [he,Subgroup.center_prod,GorensteinWalter.psl2_center_eq_bot F,bot_prod_bot,card_bot]
  obtain ⟨φ,hφ,hi,hmark,_⟩ :=
    h.exists_faithful_inner_moduleQuotientAction f hn hs hK hp ho hm hmod hP hc
  let e := MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hZ)
  let κ : moduleFrattiniImage D H →* B :=
    e.symm.toMonoidHom.comp (φ.codRestrict (MulAut.innerSubgroup B) (fun a => hi ⟨a,rfl⟩))
  have hκ (a) : MulAut.conj (κ a) = φ a :=
    MonoidHom.apply_ofInjective_symm (MulAut.conj_injective_of_center_eq_bot hZ) _
  have hki : Function.Injective κ := by
    intro a a' heq
    apply hφ
    rw [←hκ a,←hκ a',heq]
  have hconj (a) (x) : b (κ a*x*(κ a)⁻¹) =
      (a : MulAut (CoreFrattiniSection T L H)) * b x *
        (a : MulAut (CoreFrattiniSection T L H))⁻¹ := by
    rw [←hmark,←hκ]
    rfl
  have hlift (a) : ∃ k : enlargedResidual T L H,
      (k:G) ∈ (localJoin T L).pCoreIn 2 ∧
      κ a = QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k ∧
      ∀ w ∈ h.moduleCoreSpan hn, (a : MulAut (CoreFrattiniSection T L H)) w =
        b (κ a) w := by
    obtain ⟨k,hk,_,_,hkconj,hw⟩ :=
      h.exists_module_actor_agrees_on_core_span f hn hs hK hp ho hm hmod hP hc a
    have he : κ a = QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) k := by
      apply MulAut.conj_injective_of_center_eq_bot hZ
      apply MulEquiv.ext
      intro x
      apply h.coreQuotientFrattiniAction_injective hn
      change b (κ a*x*(κ a)⁻¹) = b (_*x*_)
      rw [hconj,hkconj,map_mul,map_mul,map_inv]
    refine ⟨k,hk,he,?_⟩
    simpa only [he] using hw
  have hle : κ.range ≤ quotientImage (enlargedResidual T L H) (T : Subgroup G) ⊓
      centralizer (quotientImage (enlargedResidual T L H) P : Set _) := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨k,hk,he,_⟩ := hlift a
    rw [he,←h.collapsed_quotient_core_centralizer hs.toLocalInput hc,
      ←h.collapsed_join_core_image f hs.toLocalInput hP hc]
    exact mem_map_of_mem _ hk
  have hfour : Nat.card κ.range = 4 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hki).toEquiv]
    exact (h.collapsed_moduleFrattiniImage_bot_or_four f hn hs.toLocalInput hP hc).resolve_left hne
  have hc4 : Nat.card (quotientImage (enlargedResidual T L H) (T : Subgroup G) ⊓
      centralizer (quotientImage (enlargedResidual T L H) P : Set _) : Subgroup B) = 4 := by
    rw [←h.collapsed_quotient_core_centralizer hs.toLocalInput hc]
    have h8 : p % 8 = 3 ∨ p % 8 = 5 := by omega
    exact h.collapsed_quotient_core_card hn hs hK hp ho hm h8 hc
  refine ⟨κ,hki,eq_of_le_of_card_ge hle (by rw [hfour,hc4]),?_,hconj⟩
  apply MonoidHom.ext
  intro a
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  exact (hlift a).choose_spec.2.2 w w.property

/-- Under the explicit nontrivial-image guard, every original quotient
displacement lies in the actual span and the quotient acts faithfully there. -/
theorem Data.coreSpanQuotientAction_faithful (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    (∀ (x : XiQuotient (enlargedResidual T L H)) (w : CoreFrattiniSection T L H),
      w⁻¹ * h.coreQuotientFrattiniAction hn x w ∈ h.moduleCoreSpan hn) ∧
      Function.Injective (h.coreSpanQuotientAction hn) := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
  let : IsElementaryAbelian 2 (CoreFrattiniSection T L H) := isElementaryAbelian_quotient_frattini
  let : CommGroup (CoreFrattiniSection T L H) := IsMulCommutative.instCommGroup
  let : IsQuasisimple (XiQuotient I) := hs.quasisimple
  let : Group.IsPerfect (XiQuotient I × XiQuotient I) := ⟨by
    rw [_root_.commutator_def,←top_prod_top,commutator_prod_prod]
    simp only [←_root_.commutator_def,Group.IsPerfect.commutator_eq_top,top_prod_top]⟩
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  let : Group.IsPerfect (XiQuotient (enlargedResidual T L H)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨κ,_,hκ,_,hmark⟩ := h.exists_coreSpan_inner_embedding f hn hs hK hp ho hm hmod hP hc hne
  have hgen : normalClosure (κ.range : Set (XiQuotient (enlargedResidual T L H))) = ⊤ := by
    rw [hκ]
    exact h.cubic_sylow_centralizer_generates hn hs hK hp ho hm hmod hc
  exact faithful_span_restriction (h.coreQuotientFrattiniAction hn)
    (h.coreQuotientFrattiniAction_injective hn) (pCore_quotient_pCore_eq_bot 2)
    (h.moduleCoreSpan hn) (h.moduleCoreSpan_invariant hn)
    (moduleFrattiniImage D H).subtype κ hgen
    (h.module_displacement_mem_coreSpan s.full_eq_local hn) hmark

/-- Faithfulness of the original module action also survives restriction to
the same span; the original nontrivial-image branch still has order four. -/
theorem Data.coreSpanModuleAction_faithful (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    Function.Injective (h.coreSpanModuleAction s.full_eq_local hn) ∧
      Nat.card (h.coreSpanModuleAction s.full_eq_local hn).range = 4 := by
  obtain ⟨κ,hκ,_,he,_⟩ := h.exists_coreSpan_inner_embedding f hn hs hK hp ho hm hmod hP hc hne
  have hb := (h.coreSpanQuotientAction_faithful f hn hs hK hp ho hm hmod hP hc hne).2
  have hi : Function.Injective (h.coreSpanModuleAction s.full_eq_local hn) := by
    rw [he]
    exact hb.comp hκ
  refine ⟨hi,?_⟩
  rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  exact (h.collapsed_moduleFrattiniImage_bot_or_four f hn hs.toLocalInput hP hc).resolve_left hne

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The unchanged original source retains its trivial-image branch. In the
nontrivial branch it supplies a faithful containing-quotient action on the
actual module-core span, with the original four-group, cubic mark, quadratic
action, and fixed-index bound sixteen. -/
theorem SourceCubicNormalizerEnlargement.exists_faithful_coreSpan_actions
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      ∃ hfull : D.fullModule = D.moduleSubgroup,
      ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      (moduleFrattiniImage D H = ⊥ ∨
        Nat.card (moduleFrattiniImage D H) = 4 ∧
        Function.Injective (h.coreSpanQuotientAction hn) ∧
        Function.Injective (h.coreSpanModuleAction hfull hn) ∧
        (∀ (x : XiQuotient (enlargedResidual T L H)) (w : CoreFrattiniSection T L H),
          w⁻¹ * h.coreQuotientFrattiniAction hn x w ∈ h.moduleCoreSpan hn) ∧
        ∃ κ : moduleFrattiniImage D H →* XiQuotient (enlargedResidual T L H),
          Function.Injective κ ∧
          κ.range = quotientImage (enlargedResidual T L H) (T : Subgroup G) ⊓
            centralizer (quotientImage (enlargedResidual T L H) P : Set _) ∧
          h.coreSpanModuleAction hfull hn = (h.coreSpanQuotientAction hn).comp κ ∧
          let _ : MulDistribMulAction (moduleFrattiniImage D H) (h.moduleCoreSpan hn) :=
            MulDistribMulAction.compHom _ (h.coreSpanModuleAction hfull hn)
          commutatorAction₂ (moduleFrattiniImage D H) (h.moduleCoreSpan hn) = ⊥ ∧
          (FixedPoints.subgroup (moduleFrattiniImage D H) (h.moduleCoreSpan hn)).index ≤ 16) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  refine ⟨H,P,h,s.full_eq_local,hn,hs.toLocalInput,?_⟩
  by_cases hne : moduleFrattiniImage D H = ⊥
  · exact Or.inl hne
  · right
    obtain ⟨hd,hb⟩ := h.coreSpanQuotientAction_faithful f hn hs hK hp ho hm h24 hP hcollapse hne
    have ha := (h.coreSpanModuleAction_faithful f hn hs hK hp ho hm h24 hP hcollapse hne).1
    obtain ⟨κ,hκ,hr,he,_⟩ := h.exists_coreSpan_inner_embedding f hn hs hK hp ho hm h24 hP hcollapse hne
    exact ⟨(h.collapsed_moduleFrattiniImage_bot_or_four f hn hs.toLocalInput hP hcollapse).resolve_left hne,
      hb,ha,hd,κ,hκ,hr,he,h.coreSpanModuleAction_quadratic s.full_eq_local hn,
      h.coreSpanModuleAction_fixed_index f hn hs.toLocalInput hP hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
