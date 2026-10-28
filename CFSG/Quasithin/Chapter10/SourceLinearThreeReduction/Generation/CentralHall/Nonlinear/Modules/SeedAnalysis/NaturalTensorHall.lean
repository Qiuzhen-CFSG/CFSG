module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorGeneration
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FieldKernel
public import Theory.Representation.SemilinearFixedPointCentralizer
public import Theory.Representation.OrthogonalFourPlusMatrix.LinearFactorInner
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.InnerPlacement

/-!
# The original central Hall subgroup in the split tensor Cartan

The local tensor seed is normal in T, so it has a nonzero T-fixed vector.
These fixed vectors lie in Ω₁Z(T), centralized by the given H. The seed's
TI property therefore makes H intersect M preserve it. Fixed-field descent
then makes every odd element of this overlap field-linear on the seed.

The original component action has a field-linear lift on two natural
columns, so it is inner. Apply this to B and its exchanger conjugate to
retain both component actions. The proved coprime section-kernel lifting
places the literal B in L₀. Its common marked Cartan and exponent bound
follow with the original Sylow intersection and quotient maps unchanged.
No equality of the seed and the full M-orbit module is needed.

Consumer: NaturalTensorCartan compares the original E.2.2 Cartan at the
actual tensor field degree. The exchanged-actor comparison excluding n > 2
remains necessary for the central Hall source theorem.
Source: Aschbacher--Smith 9.2.5--6 and 10.2.3, pp.731,745,
refs/quasithin.pdf. Fixed-field descent replaces the primitive-divisor step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance tensorHallSeedElementary : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance tensorHallBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
variable {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
include c hn e ht htn hsep

/-- The original local seed has a nonidentity Sylow-fixed element. -/
theorem original_even_seed_fixed_ne_bot :
    D.seed ⊓ centralizer (T : Set G) ≠ ⊥ := by
  have hE := original_even_seed_hypothesisE61 D c n hn e ht htn hsep
  let : Nontrivial D.seed := (nontrivial_iff_ne_bot D.seed).mpr D.seed_ne_bot
  let j : T →* normalizer (D.seed : Set G) := inclusion hE.sylow_le_normalizer
  let ρ := (originalSeedNormalizerAction D).comp j
  obtain ⟨v,hv,hfix⟩ := SemilinearFixedPointCentralizer.exists_nonzero_fixed ρ ⊤
    (T.isPGroup'.to_subgroup ⊤)
  have hc : (v.toMul : G) ∈ centralizer (T : Set G) := by
    intro a ha
    have hh := congrArg (fun w : Additive D.seed => (w.toMul : G))
      (hfix ⟨⟨a,ha⟩,mem_top _⟩)
    change a*(v.toMul:G)*a⁻¹ = (v.toMul:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  intro he
  have hh : (v.toMul : G) = 1 := mem_bot.mp (he ▸ (show
    (v.toMul : G) ∈ D.seed ⊓ centralizer (T : Set G) from ⟨v.toMul.property,hc⟩))
  exact hv (Additive.toMul.injective (Subtype.ext hh))

/-- The literal Sylow-fixed seed subgroup lies in the original omega-center. -/
theorem original_even_seed_fixed_le_omegaCenter :
    D.seed ⊓ centralizer (T : Set G) ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
  have hE := original_even_seed_hypothesisE61 D c n hn e ht htn hsep
  intro v hv
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hE.le_sylow hv.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv.1,hv.2⟩

/-- The actual H-star overlap preserves the original tensor seed. -/
theorem original_even_overlap_normalizes_seed :
    H ⊓ D.maximalLocal ≤ normalizer (D.seed : Set G) := by
  have hE := original_even_seed_hypothesisE61 D c n hn e ht htn hsep
  have hH : H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp c.central)
  exact (le_inf inf_le_right (inf_le_left.trans (hH.trans (centralizer_le
    (original_even_seed_fixed_le_omegaCenter D c n hn e ht htn hsep))))).trans
      (hE.localCentralizer_le_normalizer
        (original_even_seed_fixed_ne_bot D c n hn e ht htn hsep) inf_le_left)

/-- In particular, the prescribed original Hall group preserves that seed. -/
theorem original_even_hall_normalizes_seed :
    B.map H.subtype ≤ normalizer (D.seed : Set G) :=
  (le_inf (map_subtype_le B) (map_le_iff_le_comap.mpr c.hall_le)).trans
    (original_even_overlap_normalizes_seed D c n hn e ht htn hsep)


/-- Whole-seed coordinates make every odd overlap actor field-linear. -/
theorem original_even_hall_linear_coordinates :
    ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ α : MulAut SL(2,GaloisField 2 n),
        ∃ f : Additive D.seed ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n),
          (∀ g v, f (originalSeedAction D g v) =
            representation (NaturalTensor.marking α (q g)) (f v)) ∧
          ∀ (x : G) (hx : x ∈ H ⊓ D.maximalLocal), Odd (orderOf x) →
            ∀ (a : GaloisField 2 n) (v : Additive D.seed), f (originalSeedNormalizerAction D
              ⟨x,original_even_overlap_normalizes_seed D c n hn e ht htn hsep hx⟩
                (f.symm (a • f v))) =
              a • f (originalSeedNormalizerAction D
                ⟨x,original_even_overlap_normalizes_seed D c n hn e ht htn hsep hx⟩ v) := by
  obtain ⟨q,hq,hker,hl,hr,α,f,heq,φ,hφ⟩ :=
    original_even_seed_ambient_semilinear D c n hn e ht htn hsep
  have hE := original_even_seed_hypothesisE61 D c n hn e ht htn hsep
  let P := D.maximalLocal ⊓ normalizer (D.seed : Set G)
  let j : P →* normalizer (D.seed : Set G) := inclusion inf_le_right
  have hj (p : P) : j p = ⟨(p:G),p.property.2⟩ :=
    Subtype.ext (Subgroup.coe_inclusion _ p)
  let ρ : Representation (ZMod 2) P (Mat (F := GaloisField 2 n)) :=
    f.conjRingEquiv.toMonoidHom.comp ((originalSeedNormalizerAction D).comp j)
  have hsemi : ∀ p : P, ∃ σ : GaloisField 2 n ≃+* GaloisField 2 n,
      ∀ a v, ρ p (a • v) = σ a • ρ p v := by
    intro p
    refine ⟨φ p,fun a v => ?_⟩
    have hh := hφ p a (f.symm v)
    change f (originalSeedNormalizerAction D (j p) (f.symm (a • v))) =
      φ p a • f (originalSeedNormalizerAction D (j p) (f.symm v))
    rw [hj]
    simpa only [f.apply_symm_apply] using hh
  have hTP : (T : Subgroup G) ≤ P := le_inf hE.sylow_le hE.sylow_le_normalizer
  have hS : IsPGroup 2 ((T : Subgroup G).subgroupOf P) :=
    T.isPGroup'.of_injective (subgroupOfEquivOfLe hTP).toMonoidHom
      (subgroupOfEquivOfLe hTP).injective
  refine ⟨q,hq,hker,hl,hr,α,f,heq,?_⟩
  intro x hx ho
  let p : P := ⟨x,hx.2,original_even_overlap_normalizes_seed D c n hn e ht htn hsep hx⟩
  have hop : Odd (orderOf p) := by
    exact (orderOf_injective P.subtype P.subtype_injective p) ▸ ho
  have hlin := SemilinearFixedPointCentralizer.linear_of_odd_of_fixes_invariants
    ρ hsemi ((T : Subgroup G).subgroupOf P) hS p hop (by
      intro w hw
      let v := f.symm w
      have hvT : (v.toMul:G) ∈ centralizer (T : Set G) := by
        intro a ha
        let a' : (T : Subgroup G).subgroupOf P := ⟨⟨a,hTP ha⟩,ha⟩
        have hh := congrArg (fun z => ((f.symm z).toMul:G)) (hw a')
        change ((f.symm (f (originalSeedNormalizerAction D (j a') v))).toMul:G) = (v.toMul:G) at hh
        rw [f.symm_apply_apply] at hh
        change a*(v.toMul:G)*a⁻¹ = (v.toMul:G) at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      have hz := original_even_seed_fixed_le_omegaCenter D c n hn e ht htn hsep
        (show (v.toMul:G) ∈ D.seed ⊓ centralizer (T : Set G) from ⟨v.toMul.property,hvT⟩)
      have hc : H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp c.central)
      have hv : originalSeedNormalizerAction D (j p) v = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change x*(v.toMul:G)*x⁻¹ = (v.toMul:G)
        rw [←hc hx.1 _ hz,mul_inv_cancel_right]
      change f (originalSeedNormalizerAction D (j p) v) = w
      rw [hv]
      exact f.apply_symm_apply w)
  intro a v
  have hh := hlin a (f v)
  change f (originalSeedNormalizerAction D (j p) (f.symm (a • f v))) =
    a • f (originalSeedNormalizerAction D (j p) (f.symm (f v))) at hh
  rw [hj] at hh
  simpa only [f.symm_apply_apply] using hh


/-- Every odd original overlap element normalizing L induces an inner
component automorphism, using the actual whole-seed tensor coordinates. -/
theorem original_even_odd_component_inner
    (x : G) (hxH : x ∈ H) (hxM : x ∈ D.maximalLocal)
    (hxL : x ∈ normalizer (L : Set G)) (ho : Odd (orderOf x)) :
    normalizerPCoreQuotientAction L ⟨x,hxL⟩ ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  obtain ⟨q,_hq,_hk,hl,_hr,α,f,heq,hlin⟩ :=
    original_even_hall_linear_coordinates D c n hn e ht htn hsep
  let e₁ := e.trans α.symm
  let a := normalizerPCoreQuotientAction L ⟨x,hxL⟩
  let b := MulAut.congr e₁ a
  let s : normalizer (D.seed : Set G) :=
    ⟨x,original_even_overlap_normalizes_seed D c n hn e ht htn hsep ⟨hxH,hxM⟩⟩
  let E₀ := f.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
    ((originalSeedNormalizerAction D).asGroupHom s)).trans f)
  let E : Mat (F := GaloisField 2 n) ≃ₗ[GaloisField 2 n] Mat (F := GaloisField 2 n) :=
    { E₀.toAddEquiv with
      map_smul' := by
        intro a v
        have hh := hlin x ⟨hxH,hxM⟩ ho a (f.symm v)
        change f (originalSeedNormalizerAction D s (f.symm (a • v))) =
          a • f (originalSeedNormalizerAction D s (f.symm v))
        simpa only [f.apply_symm_apply] using hh }
  have hf (l : L) (v : Additive D.seed) :
      f (originalSeedAction D ⟨l,le_componentOrbit L T l.property⟩ v) =
        (e₁ (QuotientGroup.mk' (pCore 2 L) l)).val * f v := by
    have hh := heq ⟨l,le_componentOrbit L T l.property⟩ v
    rw [hl] at hh
    change _ = (α.symm (e (QuotientGroup.mk' _ l))).val * f v * (NaturalTensor.dual 1)⁻¹.val at hh
    simpa only [map_one,inv_one,Matrix.SpecialLinearGroup.coe_one,mul_one,e₁,MulEquiv.trans_apply] using hh
  have hinter (g : SL(2,GaloisField 2 n)) (v : Mat (F := GaloisField 2 n)) :
      E (g.val * v) = (b g).val * E v := by
    obtain ⟨l,rfl⟩ := (e₁.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    let l' := L.normalizerMonoidHom ⟨x,hxL⟩ l
    have he : b (e₁ (QuotientGroup.mk' (pCore 2 L) l)) =
        e₁ (QuotientGroup.mk' (pCore 2 L) l') := by
      change e₁ (a (e₁.symm (e₁ (QuotientGroup.mk' (pCore 2 L) l)))) = _
      rw [e₁.symm_apply_apply]
      change e₁ (quotientAut (pCore 2 L) _ _) = _
      rw [quotientAut_apply_mk]
    change E ((e₁ (QuotientGroup.mk' (pCore 2 L) l)).val * v) =
      (b (e₁ (QuotientGroup.mk' (pCore 2 L) l))).val * E v
    rw [he]
    have hcomm : originalSeedNormalizerAction D s
        (originalSeedAction D ⟨l,le_componentOrbit L T l.property⟩ (f.symm v)) =
      originalSeedAction D ⟨l',le_componentOrbit L T l'.property⟩
        (originalSeedNormalizerAction D s (f.symm v)) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change x*((l:G)*((f.symm v).toMul:G)*(l:G)⁻¹)*x⁻¹ =
        (x*(l:G)*x⁻¹)*(x*((f.symm v).toMul:G)*x⁻¹)*(x*(l:G)*x⁻¹)⁻¹
      group
    change f (originalSeedNormalizerAction D s
      (f.symm ((e₁ (QuotientGroup.mk' (pCore 2 L) l)).val * v))) =
      (e₁ (QuotientGroup.mk' (pCore 2 L) l')).val *
        f (originalSeedNormalizerAction D s (f.symm v))
    conv_lhs => rw [←f.apply_symm_apply v,←hf,f.symm_apply_apply]
    rw [hcomm,hf]
  obtain ⟨g,hg⟩ := linear_left_intertwiner_inner b E hinter
  refine ⟨e₁.symm g,?_⟩
  apply (MulAut.congr e₁).injective
  rw [MulAut.congr_conj,e₁.apply_symm_apply]
  exact hg.symm



open HallGeometry

/-- The actual Hall action is inner on both original components, retaining
its literal quotient map and the original exchanger. -/
theorem original_even_hall_action_inner (b : B) :
    action D B c.hall_le b ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L)) := by
  let M := D.maximalLocal
  let N := (normalizer (L : Set G)).subgroupOf M
  have htM : t ∈ M := le_normalizer_componentOrbit L T ht
  have hbM : (b : G) ∈ M := c.hall_le b.property
  have hi : N.index = 2 := normalizer_relIndex_eq_two_of_pair M L
    (L.map (MulAut.conj t).toMonoidHom)
    (source_nonnormal_maximal_pair D c.nonnormal ht htn) t htM
    (fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he))
  let : N.Normal := normal_of_index_eq_two hi
  let x : G := t⁻¹*(b : G)*t
  have hxM : x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem htM) hbM) htM
  have hxH : x ∈ H := H.mul_mem
    (H.mul_mem (H.inv_mem (c.hstar.1.1.2 ht)) b.val.property) (c.hstar.1.1.2 ht)
  have hxL : x ∈ normalizer (L : Set G) := by
    have hbN : (⟨b,hbM⟩ : M) ∈ N := hall_normalizes_component D c
      (mem_map_of_mem H.subtype b.property)
    have hh := (inferInstance : N.Normal).conj_mem _ hbN (⟨t,htM⟩ : M)⁻¹
    change t⁻¹*(b : G)*(t⁻¹)⁻¹ ∈ normalizer (L : Set G) at hh
    simpa only [inv_inv] using hh
  have hxo : Odd (orderOf x) := by
    have he := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom
      (MulAut.conj t⁻¹).injective (b : G)
    have ho : Odd (orderOf (b : G)) := by
      have hb := (hall_odd D c).of_dvd_nat (orderOf_dvd_natCard b)
      rwa [←orderOf_injective (H.subtype.comp B.subtype)
        (H.subtype_injective.comp B.subtype_injective) b] at hb
    have ho' : Odd (orderOf ((MulAut.conj t⁻¹).toMonoidHom (b : G))) := he.symm ▸ ho
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using ho'
  have hbo : Odd (orderOf (b : G)) := by
    have hb := (hall_odd D c).of_dvd_nat (orderOf_dvd_natCard b)
    rwa [←orderOf_injective (H.subtype.comp B.subtype)
      (H.subtype_injective.comp B.subtype_injective) b] at hb
  obtain ⟨a,ha⟩ := original_even_odd_component_inner D c n hn e ht htn hsep
    b b.val.property hbM (hall_normalizes_component D c
      (mem_map_of_mem H.subtype b.property)) hbo
  obtain ⟨a',ha'⟩ := original_even_odd_component_inner D c n hn e ht htn hsep x hxH hxM hxL hxo
  let R := localOrbit T L
  let S := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : IsSimpleGroup S :=
    ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := GaloisField 2 n))).trans
        QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨f,hf,hk,hfirst,hsecond⟩ := marked_pair_projection D e c.nonnormal ht htn
  let q : (R ⧸ pCore 2 R) ≃* (S × S) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hq (r : R) : q (QuotientGroup.mk' (pCore 2 R) r) = f r := rfl
  let α := MulAut.congr q (action D B c.hall_le b)
  have hα (r : R) : α (f r) =
      f (R.normalizerMonoidHom ⟨b,hbM⟩ r) := by
    rw [←hq]
    change q (action D B c.hall_le b (q.symm (q (QuotientGroup.mk' (pCore 2 R) r)))) = _
    rw [q.symm_apply_apply]
    change q (quotientAut (pCore 2 R) _ _) = _
    rw [quotientAut_apply_mk,hq]
    rfl
  have h1 (z : S) : α (z,1) = (e a * z * (e a)⁻¹,1) := by
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) z
    change α (e (QuotientGroup.mk' (pCore 2 L) l),1) = _
    rw [←hfirst,hα]
    let l' := L.normalizerMonoidHom ⟨b,hall_normalizes_component D c
      (mem_map_of_mem H.subtype b.property)⟩ l
    have he : R.normalizerMonoidHom ⟨b,hbM⟩
      ⟨l,le_componentOrbit L T l.property⟩ = ⟨l',le_componentOrbit L T l'.property⟩ := rfl
    rw [he,hfirst]
    congr 1
    have hh := MulEquiv.congr_fun ha (QuotientGroup.mk' (pCore 2 L) l)
    change _ = quotientAut (pCore 2 L) _ _ at hh
    rw [quotientAut_apply_mk] at hh
    exact (congrArg e hh).symm.trans
      ((e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _) (e.map_inv _)))
  have h2 (z : S) : α (1,z) = (1,e a' * z * (e a')⁻¹) := by
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) z
    change α (1,e (QuotientGroup.mk' (pCore 2 L) l)) = _
    rw [←hsecond,hα]
    let l' := L.normalizerMonoidHom ⟨x,hxL⟩ l
    have he : R.normalizerMonoidHom ⟨b,hbM⟩ (originalConjugateOrbitInclusion ht l) =
        originalConjugateOrbitInclusion ht l' := by
      apply Subtype.ext
      change (b : G)*(t*(l : G)*t⁻¹)*(b : G)⁻¹ = t*(x*(l : G)*x⁻¹)*t⁻¹
      dsimp [x]
      group
    rw [he,hsecond]
    congr 1
    have hh := MulEquiv.congr_fun ha' (QuotientGroup.mk' (pCore 2 L) l)
    change _ = quotientAut (pCore 2 L) _ _ at hh
    rw [quotientAut_apply_mk] at hh
    exact (congrArg e hh).symm.trans
      ((e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _) (e.map_inv _)))
  have he : α = MulAut.conj (e a,e a') := by
    apply MulEquiv.ext
    intro z
    have hz : z = (z.1,1)*(1,z.2) := by simp
    rw [hz,map_mul,h1,h2]
    simp only [Prod.mk_mul_mk,one_mul,mul_one,MulAut.conj_apply,Prod.inv_mk]
  refine ⟨q.symm (e a,e a'),?_⟩
  apply (MulAut.congr q).injective
  rw [MulAut.congr_conj,q.apply_symm_apply]
  exact he.symm

/-- All field factors have vanished on the original Hall subgroup; coprime
section-kernel lifting places that subgroup in the original component orbit. -/
theorem original_even_hall_le_orbit : B.map H.subtype ≤ localOrbit T L := by
  obtain ⟨q,_hq,_hk,_hl,_hr,_α,_f,_heq,_hlin⟩ :=
    original_even_hall_linear_coordinates D c n hn e ht htn hsep
  let q' : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
      (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) :=
    (QuotientGroup.quotientMulEquivOfEq _hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q _hq)
  exact HallGeometry.hall_le_orbit_of_inner D c e q'
    (original_even_hall_action_inner D c n hn e ht htn hsep)

/-- The original Hall exponent divides the split-torus exponent. The two
characters retain the original Hall carrier and the full section faithfulness. -/
theorem original_even_hall_exponent_dvd_sub_one :
    Monoid.exponent B ∣ 2^n-1 := by
  obtain ⟨e',q,φ,χ,_hl,_hS,_ho,hk,hχ,hexp,_hact,_hd⟩ :=
    HallGeometry.exists_hall_field_kernel_coordinates D c e
  have hle := original_even_hall_le_orbit D c n hn e ht htn hsep
  have htop : φ.ker = ⊤ := by
    rw [hk]
    apply eq_top_iff.mpr
    intro b _
    exact hle (mem_map_of_mem H.subtype b.property)
  have he : Monoid.exponent B = Monoid.exponent φ.ker := by
    rw [htop]
    exact Monoid.exponent_eq_of_mulEquiv Subgroup.topEquiv.symm
  rw [←he,GaloisField.card 2 n (by omega)] at hexp
  exact hexp


/-- The actual prescribed Hall subgroup lies in a common marked split
Cartan of L₀. Both the original component and the original Sylow intersection
are retained in the coordinates. -/
theorem original_even_hall_cartan_coordinates :
    ∃ (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L),
      IsHallSubgroup Subgroup.OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
      B.map H.subtype ≤ C ∧
      ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
        (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
          (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)))
        (d : C →* (GaloisField 2 n)ˣ × (GaloisField 2 n)ˣ), Function.Bijective d ∧
        (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
          ⟨l,le_componentOrbit L T l.property⟩) =
            (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
        ((T : Subgroup G).subgroupOf (localOrbit T L)).map
          (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
            (Matrix.SpecialLinearGroup.upperUnipotent (GaloisField 2 n)).prod
              (Matrix.SpecialLinearGroup.upperUnipotent (GaloisField 2 n)) ∧
        ∀ x : C, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
          ⟨x,((hC.trans (map_subtype_le (pResidual 2
            (sourceOrbitSylowNormalizer T L)))).trans inf_le_left) x.property⟩) =
          (Matrix.SpecialLinearGroup.diag2 ((d x).1 : GaloisField 2 n) (Units.ne_zero _),
            Matrix.SpecialLinearGroup.diag2 ((d x).2 : GaloisField 2 n) (Units.ne_zero _)) := by
  obtain ⟨C,hC,hHall,_hBC,hplus,e',q,d,hd,hl,hS,hdiag⟩ :=
    HallGeometry.exists_hall_invariant_source_borel_marking D c e
  have hBR := original_even_hall_le_orbit D c n hn e ht htn hsep
  rw [inf_eq_left.mpr hBR] at hplus
  exact ⟨C,hC,hHall,hplus,e',q,d,hd,hl,hS,hdiag⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
