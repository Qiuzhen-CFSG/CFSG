module
public import Theory.Representation.BinaryOffender.SquareZeroSaturation
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.InitialDetection
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ConstituentInner
public import Theory.Representation.SL3.NaturalNormalizerFixed
public import Theory.Representation.BinaryOffender.Embedding
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Saturation forced by a nontrivial whole-action kernel

Let E = Ω₁(Z(Q)) for Q = [O₂(KR),K], with C_Q(K)=1. A nontrivial
kernel of the projection from the faithful E-action to the initial action
contains an involution centralizing any prescribed elementary offender D.
Its displacement map has square zero and commutes with the component and D.
Its nonzero image contains a natural Irr⁺ constituent, costing at least n
binary dimensions under D. The same image is a quotient of E modulo that
image, so the two section costs force fixed codimension at least 2n.

For the selected minimal moving offender, the proved automorphism rank
bound is 2n. Thus a nontrivial kernel forces equality: D has order 2^(2n),
fixed codimension 2n and weight dim(E). In particular a strong minimal
moving offender eliminates the whole-action kernel. The original maximum
elementary subgroup has the same weight. The final dichotomy retains this
saturated branch; in the other branch the offender lies in the actual
component and the whole central omega equals the initial moved subgroup.

A nontrivial quotient scalar now sharpens the saturated branch: the actual
kernel involution has image and kernel equal to one natural constituent, and
the entire central omega is an extension of that constituent by another copy
at the same marking. Its binary dimension is exactly 6n. This proves natural
or doubled-natural order for the whole central omega whenever such a scalar
exists, including field four. It does not assert splitting of the extension.

NonblockKernelSaturation supplies the literal original 4.3.8--10 application.
Splitting, the whole center and the common-marked upper/Frattini sections
remain open. No field-four covering kernel or constituent marking is lost.
Source: Aschbacher--Smith B.1.5(8), B.7.2, K.3.2 and C.1.34, printed
pp.69--70,119,454--456,136--137; the square-zero section budget is elementary
linear algebra.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
set_option backward.isDefEq.respectTransparency false

private theorem square_zero_budget
    {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (f : V →ₗ[ZMod 2] V)
    (hf : ∀ v, f (f v) = 0) (hc : ∀ x v, f (ρ x v) = ρ x (f v))
    (W : Subrepresentation ρ) (hW : W.toSubmodule = f.range) (A : Subgroup X) :
    2 * fixedCodim W.toRepresentation A ≤ fixedCodim ρ A := by
  let g : V →ₗ[ZMod 2] W.toSubmodule := f.codRestrict _ (fun v => hW.symm ▸ ⟨v,rfl⟩)
  have hk : W.toSubmodule ≤ g.ker := by
    intro v hv
    obtain ⟨w,rfl⟩ := hW ▸ hv
    exact Subtype.ext (hf w)
  let q : (V ⧸ W.toSubmodule) →ₗ[ZMod 2] W.toSubmodule := W.toSubmodule.liftQ g hk
  have hq : Function.Surjective q := by
    rintro ⟨v,hv⟩
    obtain ⟨w,hw⟩ := hW ▸ hv
    exact ⟨W.toSubmodule.mkQ w,Subtype.ext hw⟩
  have he (x : X) (v : V ⧸ W.toSubmodule) :
      q (W.quotientRepresentation x v) = W.toRepresentation x (q v) := by
    obtain ⟨w,rfl⟩ := W.toSubmodule.mkQ_surjective v
    exact Subtype.ext (hc x w)
  have hl := fixedCodim_le_of_equivariant_surjection W.quotientRepresentation
    W.toRepresentation q hq he A
  have hb := fixedCodim_quotient_add_subrepresentation_le ρ W A
  omega

private theorem natural_cost
    {F X : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group X]
    {n : ℕ} (hF : Nat.card F = 2^n)
    (B : Subgroup X) [B.Normal] (e : B ≃* SL(3,F))
    (ρ : Representation (ZMod 2) X (Fin 3 → F)) (hf : Function.Injective ρ)
    (hb : ∀ (b : B) v, ρ b v = (e b).val.mulVec v)
    (A : Subgroup X) (hne : A ≠ ⊥) : n ≤ fixedCodim ρ A := by
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hne
  let t : (Fin 3 → F) ≃+ (Fin 3 → F) := AddEquiv.ofBijective (ρ a).toAddMonoidHom
    (ρ.apply_bijective a)
  have ht : t ≠ AddEquiv.refl _ := by
    intro he
    apply ha
    apply Subtype.ext
    apply hf
    change ρ a.val = ρ (1 : X)
    rw [map_one]
    exact LinearMap.ext (fun v => DFunLike.congr_fun he v)
  obtain ⟨σ,hσ⟩ := SL3OddNaturalNormalizer.normalizer_semilinear B e ρ hb a
  have hcard := SL3NaturalFixed.fixed_card_le_of_semilinear t ht σ hσ
  let j : fixedSpace ρ A → {v : Fin 3 → F // t v = v} := fun v => ⟨v,v.property a⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : {v : Fin 3 → F // t v = v} => z.val) he
  have hh := (Nat.card_le_card_of_injective j hj).trans hcard
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hF,←pow_mul] at hh
  have hr := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hh
  have hd : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  have hv : Module.finrank (ZMod 2) (Fin 3 → F) = 3*n := by
    simp [Module.finrank_pi_fintype,hd]
  have hs := fixedCodim_add_finrank ρ A
  omega

private theorem natural_cost_coordinates
    {F X W : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group X]
    [AddCommGroup W] [Module (ZMod 2) W]
    {n : ℕ} (hF : Nat.card F = 2^n)
    (B : Subgroup X) [B.Normal] (e : B ≃* SL(3,F))
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (l : W ≃ₗ[ZMod 2] (Fin 3 → F))
    (hl : ∀ (b : B) v, l (ρ b v) = specialLinearNatural 3 (e b) (l v))
    (A : Subgroup X) (hne : A ≠ ⊥) : n ≤ fixedCodim ρ A := by
  let τ : Representation (ZMod 2) X (Fin 3 → F) := l.conjRingEquiv.toMonoidHom.comp ρ
  have he (a : X) (v : W) : l (ρ a v) = τ a (l v) := by
    change l (ρ a v) = l (ρ a (l.symm (l v)))
    rw [l.symm_apply_apply]
  have hb (b : B) (v : Fin 3 → F) : τ b v = (e b).val.mulVec v := by
    change l (ρ b (l.symm v)) = _
    rw [hl,l.apply_symm_apply]
    rfl
  have hc := natural_cost hF B e τ (l.conjRingEquiv.injective.comp hf) hb A hne
  have ht := fixedCodim_map_equivariant ρ τ (MonoidHom.id X) l he A
  simp only [Subgroup.map_id] at ht
  exact ht.ge.trans' hc

open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource

private theorem natural_section_cost
    {X V : Type*} [Group X] [Finite X] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (B D : Subgroup X) [B.Normal] [IsQuasisimple B]
    (hD : D ≠ ⊥) (hd : D ⊓ centralizer (B : Set X) = ⊥)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ B I)
    (F : BinaryField) (hnat : ConstituentRecognition.HasNaturalCentralSection ρ B D I F)
    (W : Subrepresentation (ρ.comp (B ⊔ D).subtype)) (hIW : I ≤ W.toSubmodule) :
    F.degree ≤ fixedCodim W.toRepresentation (D.subgroupOf (B ⊔ D)) := by
  obtain ⟨hs,hn,⟨a⟩⟩ := hnat
  let H := B ⊔ D
  let C := B.subgroupOf H
  let U := invariantSubspace ρ H I hs
  let σ := centralSectionRepresentation ρ B H I hs hn
  let π := KernelQuotient.projection σ
  let C' := SourceCompletion.ChiefImage.component σ C
  let δ := KernelQuotient.action σ
  let := SourceCompletion.ChiefImage.component_normal σ C
  have hk := centralSection_kernel_le_centralizer ρ B H le_sup_left I hI hs hn
  have hnD : (D.subgroupOf H).map π ≠ ⊥ := by
    intro hz
    apply hD
    apply bot_unique
    intro d hdD
    have hdker : (⟨d,mem_sup_right hdD⟩ : H) ∈ σ.ker := by
      have he := (map_eq_bot_iff (D.subgroupOf H)).mp hz
        (show (⟨d,mem_sup_right hdD⟩ : H) ∈ D.subgroupOf H from hdD)
      have hh := congrArg (fun x => δ x) he
      change σ (⟨d,mem_sup_right hdD⟩ : H) = δ 1 at hh
      change σ (⟨d,mem_sup_right hdD⟩ : H) = 1
      simpa only [map_one] using hh
    exact hd.le ⟨hdD,(hk (mem_map_of_mem H.subtype hdker)).2⟩
  have hc := natural_cost_coordinates F.card_eq C' a.groupEquiv δ
    (KernelQuotient.faithful σ) a.linearEquiv a.intertwines _ hnD
  have ht := fixedCodim_map_equivariant σ δ π (LinearEquiv.refl (ZMod 2) _)
    (fun _ _ => rfl) (D.subgroupOf H)
  rw [←ht] at hc
  have hq := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation
    (centralSectionFixedSubspace ρ B H I hs hn) (D.subgroupOf H)
  change fixedCodim σ (D.subgroupOf H) + _ ≤ _ at hq
  let j : I →ₗ[ZMod 2] W.toSubmodule := Submodule.inclusion hIW
  have hj : Function.Injective j := Submodule.inclusion_injective hIW
  have he (x : H) (v : I) : W.toRepresentation x (j v) = j (U.toRepresentation x v) := rfl
  have hl : fixedCodim U.toRepresentation (D.subgroupOf H) ≤
      fixedCodim W.toRepresentation (D.subgroupOf H) := by
    have hh := fixedCodim_map_le_of_embedding
      W.toRepresentation U.toRepresentation (MonoidHom.id H) j hj he (D.subgroupOf H)
    change fixedCodim U.toRepresentation ((D.subgroupOf H).map (MonoidHom.id H)) ≤
      fixedCodim W.toRepresentation (D.subgroupOf H) at hh
    rw [Subgroup.map_id] at hh
    exact hh
  exact hc.trans ((Nat.le_add_right _ _).trans (hq.trans hl))

private theorem core_involution_centralizing
    {X : Type*} [Group X] [Finite X] (D : Subgroup X) (hp : IsPGroup 2 D)
    (hk : pCore 2 X ≠ ⊥) :
    ∃ x ∈ pCore 2 X, orderOf x = 2 ∧ x ∈ centralizer ((D ⊔ pCore 2 X : Subgroup X) : Set X) := by
  let P := D ⊔ pCore 2 X
  let N := (pCore 2 X).subgroupOf P
  have hn : N ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map P.subtype) he
    rw [map_subgroupOf_eq_of_le (show pCore 2 X ≤ P from le_sup_right),Subgroup.map_bot] at hh
    exact hk hh
  have hZ := center_inf_ne_bot_of_normal (hp.to_sup_of_normal_right pCore_isPGroup) N hn
  let Z := center P ⊓ N
  have hpZ : IsPGroup 2 Z := (hp.to_sup_of_normal_right pCore_isPGroup).to_subgroup Z
  have hd : 2 ∣ Nat.card Z := hpZ.card_eq_or_dvd.resolve_left
    (fun hc => hZ (card_eq_one.mp hc))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 hd
  refine ⟨(x.val : X),x.property.2,?_,?_⟩
  · exact (orderOf_coe x.val).trans ((orderOf_coe x).trans hx)
  · intro d hdD
    exact congrArg P.subtype (mem_center_iff.mp x.property.1 ⟨d,hdD⟩)

namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.KernelSaturation
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E := CentralSections.coreOmegaLayer_elementary
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* H)
local notation "rho" => CentralSections.coreOmegaRepresentation h hn
local notation "f" => NoncoreOffenders.toInitial h hn E
  (CentralSections.coreOmegaLayer_centralizer_le h hn)

include h hn

private theorem invariant_space_cost
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (D : Subgroup H) (hD : IsMinimalBestOffender rho D) (hm : ⁅B,D⁆ = B)
    (hd : D ⊓ centralizer (B : Set H) = ⊥)
    (W : Subrepresentation ((rho).comp (B ⊔ D).subtype)) (hne : W.toSubmodule ≠ ⊥) :
    n ≤ fixedCodim W.toRepresentation (D.subgroupOf (B ⊔ D)) := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  have hWB : B ≤ subspaceStabilizer rho W.toSubmodule := by
    apply le_subspaceStabilizer
    intro b hb v hv
    exact W.apply_mem_toSubmodule ⟨b,mem_sup_left hb⟩ hv
  have hnot : ¬ W.toSubmodule ≤ fixedSpace rho B := by
    rw [KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed]
    exact fun hw => hne (bot_unique hw)
  obtain ⟨I,hIW,hI⟩ := exists_isIrrPlus_le_of_not_fixed rho B W.toSubmodule hWB hnot
  have hc : IsComponent H B := ⟨(inferInstance : (B).Normal).isSubnormal,inferInstance⟩
  have hDI := sup_le hI.choose
    (ChapterB.SourceInduction.ComponentReduction.minimalOffender_stabilizes_irrPlus
      rho (CentralSections.coreOmegaRepresentation_injective h hn) hD hc hm hI)
  have hDN : B ⊔ D ≤ normalizer (B : Set H) := by rw [normalizer_eq_top]; exact le_top
  have hff := centralSection_isFFModule_of_offender rho B D (B ⊔ D) hD.1
    le_sup_left le_sup_right (disjoint_iff.mpr hd) I hI hDI hDN
  have hsq : IsSQTK KnownSimple.IsKnownSimple B :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) (h.sqtk.subgroup L)
      (ChapterA.Section02.IsSectionOf.of_surjective ((q).comp (L).subtype).rangeRestrict
        ((q).comp (L).subtype).rangeRestrict_surjective)
  have hnat : ConstituentRecognition.HasNaturalCentralSection rho B D I
      (ConstituentRecognition.coefficientField h hn) :=
    ⟨hDI,hDN,ConstituentRecognition.centralSection_natural rho B D hD.1.1 I hI hDI hDN
      hff hsq (ConstituentRecognition.coefficientField h hn)
      (KernelOffenders.omegaCover h hn (Classical.choice h.model)).quotientCenterEquiv⟩
  exact natural_section_cost rho B D hD.1.1.1 hd I hI
    (ConstituentRecognition.coefficientField h hn) hnat W hIW

/-- A surviving whole-action kernel forces the selected minimal moving offender
to have maximal possible rank and no excess rank over fixed codimension. -/
theorem kernel_nontrivial_saturates
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (D : Subgroup H) (hD : IsMinimalBestOffender rho D) (hm : ⁅B,D⁆ = B)
    (hd : D ⊓ centralizer (B : Set H) = ⊥) (hk : (f).ker ≠ ⊥) :
    rank D = 2*n ∧ fixedCodim rho D = 2*n ∧ Nat.card D = 2^(2*n) ∧
      weight rho D = Module.finrank (ZMod 2) (Additive E) := by
  have hcore : pCore 2 H ≠ ⊥ := by rwa [NoncoreOffenders.toInitial_kernel] at hk
  obtain ⟨x,hx,hx2,hxD⟩ := core_involution_centralizing D (hD.1.1.2.isPGroup 2 D) hcore
  have hxB : x ∈ centralizer (B : Set H) := by
    apply MovingBounds.initial_kernel_le_centralizer h hn
    rwa [NoncoreOffenders.toInitial_kernel]
  let X := B ⊔ D
  let τ := (rho).comp X.subtype
  let t : Additive E →ₗ[ZMod 2] Additive E := rho x - 1
  have hc (g : X) (v : Additive E) : t (τ g v) = τ g (t v) := by
    have hxX : x ∈ centralizer (X : Set H) := by
      have hh : X ≤ centralizer ({x} : Set H) := sup_le
        (by intro b hb y hy; rcases Set.mem_singleton_iff.mp hy with rfl; exact (hxB b hb).symm)
        (by intro d hd y hy; rcases Set.mem_singleton_iff.mp hy with rfl; exact (hxD d (mem_sup_left hd)).symm)
      intro g hg
      exact (hh hg x (Set.mem_singleton x)).symm
    change rho x (rho g.val v) - rho g.val v = rho g.val (rho x v-v)
    rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      mem_centralizer_iff.mp hxX g g.property]
  have ht (v : Additive E) : t (t v) = 0 := by
    change rho x (rho x v-v) - (rho x v-v) = 0
    have hxpow : x^2 = 1 := hx2 ▸ pow_orderOf_eq_one x
    rw [involution_fixes_displacement rho (by simpa only [pow_two] using hxpow),sub_self]
  let W : Subrepresentation τ := ⟨t.range,by
    intro g v hv
    obtain ⟨w,rfl⟩ := hv
    exact ⟨τ g w,hc g w⟩⟩
  have hne : W.toSubmodule ≠ ⊥ := by
    intro hz
    have hxone : x = 1 := by
      apply CentralSections.coreOmegaRepresentation_injective h hn
      rw [map_one]
      apply LinearMap.ext
      intro v
      have hv : t v ∈ W.toSubmodule := ⟨v,rfl⟩
      rw [hz,Submodule.mem_bot] at hv
      exact sub_eq_zero.mp hv
    simp [hxone] at hx2
  have hl := invariant_space_cost h hn hfixed D hD hm hd W hne
  change n ≤ fixedCodim W.toRepresentation (D.subgroupOf X) at hl
  have hb := square_zero_budget τ t ht hc W rfl (D.subgroupOf X)
  rw [fixedCodim_subgroupOf rho (show D ≤ X from le_sup_right)] at hb
  have hcD := MovingBounds.elementary_card_le_of_disjoint h hn D hD.1.1 hd
  have hr : rank D ≤ 2*n := by
    rw [hD.1.1.card_eq_two_pow_rank] at hcD
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hcD
  have ho := (hD.1.isOffender rho).2
  have hdims := fixedCodim_add_finrank rho D
  have hrank : rank D = 2*n := by omega
  have hcodim : fixedCodim rho D = 2*n := by omega
  refine ⟨hrank,hcodim,?_,?_⟩
  · rw [hD.1.1.card_eq_two_pow_rank,hrank]
  · unfold weight
    omega

/-- Strict offender inequality eliminates the entire initial-projection kernel,
including the exceptional field-four covering contribution. -/
theorem kernel_eq_bot_of_strong_minimal
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (D : Subgroup H) (hD : IsMinimalBestOffender rho D) (hm : ⁅B,D⁆ = B)
    (hd : D ⊓ centralizer (B : Set H) = ⊥) (hs : fixedCodim rho D < rank D) :
    (f).ker = ⊥ := by
  by_contra hk
  obtain ⟨hr,hc,_,_⟩ := kernel_nontrivial_saturates h hn hfixed D hD hm hd hk
  omega

/-- The original radical overgroup supplies either exact component containment
and central-omega exhaustion, or a saturated offender of order q². Its original
maximum elementary subgroup, weight and literal initial map are retained. -/
theorem exists_exact_or_saturated_offender
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsMinimalBestOffender rho D ∧ IsQuadratic rho D ∧
      weight rho D = weight rho (A.map q) ∧ ⁅B,D⁆ = B ∧
      D ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((f).comp D.subtype) ∧
      D ≤ B ⊔ pCore 2 H ∧ D.map f ≤ centralOmegaComponent K R ∧
      ((f).ker = ⊥ ∧ D ≤ B ∧
        Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R) =
          initialMoved K R ∨
       (f).ker ≠ ⊥ ∧ rank D = 2*n ∧ fixedCodim rho D = 2*n ∧ Nat.card D = 2^(2*n) ∧
         weight rho (A.map q) = Module.finrank (ZMod 2) (Additive E)) := by
  obtain ⟨A,hA,D,hDA,hD,hq,hw,hm,hd,hfi,hDB,hDI,_,_,_⟩ :=
    ConstituentInner.exists_minimal_component_mod_core_offender h hn hfixed S hRS
  refine ⟨A,hA,D,hDA,hD,hq,hw,hm,hd,hfi,hDB,hDI,?_⟩
  by_cases hk : (f).ker = ⊥
  · have hcore : pCore 2 H = ⊥ := by
      rw [←NoncoreOffenders.toInitial_kernel h hn E
        (CentralSections.coreOmegaLayer_centralizer_le h hn)]
      exact hk
    exact Or.inl ⟨hk,by simpa only [hcore,sup_bot_eq] using hDB,
      SmallOmega.omega_eq_initial_of_kernel_bot h hn hfixed hk⟩
  · obtain ⟨hr,hc,hcard,hweight⟩ := kernel_nontrivial_saturates h hn hfixed D hD hm hd hk
    exact Or.inr ⟨hk,hr,hc,hcard,hw ▸ hweight⟩



/-- A nontrivial quotient scalar excludes central attachments in the saturated
square-zero flag. The whole central omega is a natural self-extension of
binary dimension 6n. The actual involution centralizes the entire action
kernel, so its natural flag is invariant under that kernel. -/
theorem kernel_nontrivial_natural_flag
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1)
    (D : Subgroup H) (hD : IsMinimalBestOffender rho D) (hm : ⁅B,D⁆ = B)
    (hd : D ⊓ centralizer (B : Set H) = ⊥) (hk : (f).ker ≠ ⊥) :
    ∃ x ∈ (f).ker, orderOf x = 2 ∧ x ∈ centralizer ((B ⊔ D : Subgroup H) : Set H) ∧
      x ∈ centralizer ((f).ker : Set H) ∧
      ∃ I : Submodule (ZMod 2) (Additive E), IsIrrPlus rho B I ∧
        (rho x - 1).range = I ∧ (rho x - 1).ker = I ∧
        Module.finrank (ZMod 2) I = 3*n ∧
        Module.finrank (ZMod 2) (Additive E) = 6*n := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn e).isQuasisimple
  have hcore : pCore 2 H ≠ ⊥ := by rwa [NoncoreOffenders.toInitial_kernel] at hk
  obtain ⟨x,hx,hx2,hxD⟩ := core_involution_centralizing D (hD.1.1.2.isPGroup 2 D) hcore
  have hxB : x ∈ centralizer (B : Set H) := by
    apply MovingBounds.initial_kernel_le_centralizer h hn
    rwa [NoncoreOffenders.toInitial_kernel]
  let X := B ⊔ D
  have hxX : x ∈ centralizer (X : Set H) := by
    have hh : X ≤ centralizer ({x} : Set H) := sup_le
      (by intro b hb y hy; rcases Set.mem_singleton_iff.mp hy with rfl; exact (hxB b hb).symm)
      (by intro d hd y hy; rcases Set.mem_singleton_iff.mp hy with rfl; exact (hxD d (mem_sup_left hd)).symm)
    intro g hg
    exact (hh hg x (Set.mem_singleton x)).symm
  let τ := (rho).comp X.subtype
  let t : Additive E →ₗ[ZMod 2] Additive E := rho x - 1
  have hc (g : X) (v : Additive E) : t (τ g v) = τ g (t v) := by
    change rho x (rho g.val v) - rho g.val v = rho g.val (rho x v-v)
    rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      mem_centralizer_iff.mp hxX g g.property]
  have ht (v : Additive E) : t (t v) = 0 := by
    change rho x (rho x v-v) - (rho x v-v) = 0
    have hxpow : x^2 = 1 := hx2 ▸ pow_orderOf_eq_one x
    rw [involution_fixes_displacement rho (by simpa only [pow_two] using hxpow),sub_self]
  let W : Subrepresentation τ := ⟨t.range,by
    intro g v hv
    obtain ⟨w,rfl⟩ := hv
    exact ⟨τ g w,hc g w⟩⟩
  have hne : W.toSubmodule ≠ ⊥ := by
    intro hz
    have hxone : x = 1 := by
      apply CentralSections.coreOmegaRepresentation_injective h hn
      rw [map_one]
      apply LinearMap.ext
      intro v
      have hv : t v ∈ W.toSubmodule := ⟨v,rfl⟩
      rw [hz,Submodule.mem_bot] at hv
      exact sub_eq_zero.mp hv
    simp [hxone] at hx2
  have hWB : B ≤ subspaceStabilizer rho W.toSubmodule := by
    apply le_subspaceStabilizer
    intro b hb v hv
    exact W.apply_mem_toSubmodule ⟨b,mem_sup_left hb⟩ hv
  have hnot : ¬ W.toSubmodule ≤ fixedSpace rho B := by
    rw [KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed]
    exact fun hw => hne (bot_unique hw)
  obtain ⟨I,hIW,hI⟩ := exists_isIrrPlus_le_of_not_fixed rho B W.toSubmodule hWB hnot
  have hcomp : IsComponent H B := ⟨(inferInstance : (B).Normal).isSubnormal,inferInstance⟩
  have hXI : X ≤ subspaceStabilizer rho I := sup_le hI.choose
    (ChapterB.SourceInduction.ComponentReduction.minimalOffender_stabilizes_irrPlus
      rho (CentralSections.coreOmegaRepresentation_injective h hn) hD hcomp hm hI)
  let U := invariantSubspace rho X I hXI
  have hi := invariant_space_cost h hn hfixed D hD hm hd U hI.ne_bot
  have hmX : ⁅(B).subgroupOf X,D.subgroupOf X⁆ = (B).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le (show B ≤ X from le_sup_left),
      map_subgroupOf_eq_of_le (show D ≤ X from le_sup_right),hm]
  obtain ⟨k,_,_,hkfree⟩ := InitialDetection.exists_cubic_scalar_lift h hn hfixed e s hs hsne
  let kJ : J := ⟨k,mem_sup_left k.property⟩
  have hkB : q kJ ∈ B := ⟨⟨kJ,k.property⟩,rfl⟩
  let a : X := ⟨q kJ,mem_sup_left hkB⟩
  have hafree (v : Additive E) (hv : τ a v = v) : v = 0 := by
    have hv' := congrArg (fun w : Additive E => (w.toMul : J)) hv
    change (rho (q kJ) v).toMul.val = v.toMul.val at hv'
    rw [CentralSections.coreOmegaRepresentation_eq,
      NormalElementaryQuotient.representation_apply] at hv'
    have hve : ((v.toMul : J) : G) = 1 := by
      apply hkfree.le
      refine ⟨?_,mem_centralizer_iff.mpr ?_⟩
      · have hOC : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R) ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ K R) := by
          exact map_mono (map_subtype_le _)
        exact hOC ((CentralSections.coreOmegaLayer_eq (K := K) (R := R)).le v.toMul.property)
      · rintro y (rfl : y = (k : G))
        exact mul_inv_eq_iff_eq_mul.mp (congrArg (J).subtype hv')
    exact Additive.toMul.injective (Subtype.ext (Subtype.ext hve))
  have htotal := (kernel_nontrivial_saturates h hn hfixed D hD hm hd hk).2.1
  have hbound : fixedCodim τ (D.subgroupOf X) ≤ 2*n := by
    rw [fixedCodim_subgroupOf rho (show D ≤ X from le_sup_right),htotal]
  obtain ⟨hr,hker,hdegree⟩ := square_zero_range_ker_eq_of_saturation τ
    ((B).subgroupOf X) (D.subgroupOf X) hmX a hkB hafree t ht hc U hIW n hi hbound
  have hdim := (ConstituentRecognition.irrPlus_card_finrank h hn hfixed e I hI).2
  refine ⟨x,?_,hx2,hxX,?_,I,hI,hr,hker,hdim,?_⟩
  · rwa [NoncoreOffenders.toInitial_kernel]
  · intro y hy
    apply hxD y
    apply mem_sup_right
    rwa [NoncoreOffenders.toInitial_kernel] at hy
  · change Module.finrank (ZMod 2) (Additive E) = 2 * Module.finrank (ZMod 2) I at hdegree
    omega


/-- A nontrivial quotient scalar excludes central attachments in the saturated
square-zero flag. The whole central omega is a natural self-extension of
binary dimension 6n, retaining the actual involution in the action kernel. -/
theorem kernel_nontrivial_natural_self_extension
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1)
    (D : Subgroup H) (hD : IsMinimalBestOffender rho D) (hm : ⁅B,D⁆ = B)
    (hd : D ⊓ centralizer (B : Set H) = ⊥) (hk : (f).ker ≠ ⊥) :
    ∃ x ∈ (f).ker, orderOf x = 2 ∧ x ∈ centralizer ((B ⊔ D : Subgroup H) : Set H) ∧
      ∃ I : Submodule (ZMod 2) (Additive E), IsIrrPlus rho B I ∧
        (rho x - 1).range = I ∧ (rho x - 1).ker = I ∧
        Module.finrank (ZMod 2) I = 3*n ∧
        Module.finrank (ZMod 2) (Additive E) = 6*n := by
  obtain ⟨x,hx,hx2,hxc,_,I,hI,hr,hker,hi,ht⟩ :=
    kernel_nontrivial_natural_flag h hn hfixed e s hs hsne D hD hm hd hk
  exact ⟨x,hx,hx2,hxc,I,hI,hr,hker,hi,ht⟩



local instance binaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Both sections of the saturated flag are natural at one common marking.
The quotient equivalence is induced by the actual kernel involution's displacement;
this assertion does not assume or assert splitting of the extension. -/
theorem kernel_nontrivial_common_marking
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1)
    (D : Subgroup H) (hD : IsMinimalBestOffender rho D) (hm : ⁅B,D⁆ = B)
    (hd : D ⊓ centralizer (B : Set H) = ⊥) (hk : (f).ker ≠ ⊥) :
    ∃ α : SL(3,F) ≃* SL(3,F),
      let σ := ((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp
        (α.toMonoidHom.comp (KernelOffenders.omegaCover h hn e).toMonoidHom)
      ∃ I : Subrepresentation ((rho).comp (B).subtype),
        Nonempty (I.toRepresentation.Equiv σ) ∧ Nonempty (I.quotientRepresentation.Equiv σ) := by
  have hall := kernel_nontrivial_natural_self_extension (K := K) (R := R) (n := n)
    (F := F) (hEN := hEN) h hn hfixed e s hs hsne D hD hm hd hk
  obtain ⟨x,_,_,hxc,I,hI,hr,hker,_,_⟩ := hall
  obtain ⟨α,l,hl⟩ := ConstituentSections.irrPlus_marked_coordinates h hn hfixed e I hI
  let t : Additive E →ₗ[ZMod 2] Additive E := rho x - 1
  let U := invariantSubspace rho B I hI.choose
  have hc (b : B) (v : Additive E) : t (rho b v) = rho b (t v) := by
    change rho x (rho b.val v) - rho b.val v = rho b.val (rho x v-v)
    rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      mem_centralizer_iff.mp hxc b (mem_sup_left b.property)]
  obtain ⟨c,_,he⟩ := quotient_equiv_of_range_ker_eq ((rho).comp (B).subtype) t hc U hr hker
  refine ⟨α,U,⟨.mk l ?_⟩,⟨.mk (c.trans l) ?_⟩⟩
  · intro b
    apply LinearMap.ext
    intro v
    exact hl b v
  · intro b
    apply LinearMap.ext
    intro v
    change l (c (U.quotientRepresentation b v)) = _
    rw [he,hl]
    rfl

omit hEN in
/-- With a nontrivial quotient scalar the entire central omega has natural
or doubled-natural order. The large alternative is an exact equality. -/
theorem omega_card_eq_of_scalar
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hsne : s ≠ 1) :
    Nat.card (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
      (msQ K R)) = 2^(3*n) ∨
    Nat.card (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
      (msQ K R)) = 2^(6*n) := by
  let := CentralSections.coreOmegaLayer_normal h hn
  by_cases hk : (f).ker = ⊥
  · rw [SmallOmega.omega_eq_initial_of_kernel_bot h hn hfixed hk]
    obtain ⟨e',hm | hm⟩ := initialMoved_section_models h hn
    · left
      rw [HasSectionModel,bot_subgroupOf] at hm
      obtain ⟨_,_,_,_,b,_⟩ := hm
      rw [Nat.card_congr (QuotientGroup.quotientBot.symm.trans b).toEquiv]
      change Nat.card (Fin 3 → F) = _
      rw [Nat.card_fun,Nat.card_fin,h.field_card,←pow_mul,Nat.mul_comm n 3]
    · right
      rw [HasSectionModel,bot_subgroupOf] at hm
      obtain ⟨_,_,_,_,b,_⟩ := hm
      rw [Nat.card_congr (QuotientGroup.quotientBot.symm.trans b).toEquiv]
      change Nat.card ((Fin 3 → F) × (Fin 3 → F)) = _
      rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,h.field_card,←pow_mul,←pow_add]
      congr 1
      omega
  · right
    obtain ⟨A,hA,D,hDA,hD,hq,hw,hm,hd,_⟩ :=
      exists_exact_or_saturated_offender h hn hfixed (R.subgroupOf J) le_rfl
    obtain ⟨x,_,_,_,I,_,_,_,_,hdim⟩ :=
      kernel_nontrivial_natural_self_extension h hn hfixed e s hs hsne D hD hm hd hk
    have hzJ : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (msQ K R) ≤ J := (map_subtype_le _).trans (msQ_le_joinCore.trans (pCoreIn_le 2 _))
    have hEcard : Nat.card E = Nat.card
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
          (msQ K R)) := by
      rw [CentralSections.coreOmegaLayer_eq]
      exact Nat.card_congr (subgroupOfEquivOfLe hzJ).toEquiv
    rw [←hEcard]
    change Nat.card (Additive E) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.KernelSaturation
