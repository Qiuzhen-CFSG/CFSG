module
public import CFSG.Quasithin.ChapterB.Section02.AlternatingFivePoint
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.CoverAction
public import Theory.Representation.NormalElementaryQuotient.OriginalAction
public import Theory.Representation.BinaryAlternatingFiveBorel.PointNormalizedTwoSubgroup
public import Theory.Representation.BinaryPermutation.FiveSylowSingular
public import Theory.GroupTheory.PCoreActionCardKernel

/-!
# The full point radical above an A₅ component

Extend the marked normal A₅ action to the actual five-point permutation
action of the overgroup. Counting its component kernel and using the
outer two-group quotient identifies its full kernel with O₂(H).

A nonzero Sylow-fixed vector is singular, so its point centralizer contains
the even A₄ stabilizer of its unique zero coordinate. Every two-group
normalized by this A₄ acts evenly. The no-even-offender theorem therefore
puts the Thompson subgroup of the full point radical in the kernel, and
B.2.10 gives both Thompson and Baumann equalities with O₂(H).

The source consumer ComponentFiveBaumann applies this to the literal KT
and O₂(L₁T), with no assumed block, normalizer bound or trivial outer action.
Source: Aschbacher–Smith B.3.2(4), p.83, B.2.10(1), p.77, and 13.4.10(1),
printed p.908. The finite point check involves only sixteen vectors and
120 permutations; the two-subgroup calculation reuses the proved A₄ API.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.AlternatingFivePoint
open BinaryPermutation
variable {H : Type*} [Group H] [Finite H]

local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 5)) := Subtype.fintype _

private theorem singular_point_stabilizer (v : core (Fin 5))
    (hv : v ≠ 0) (hs : FiveGeometry.form v = 0) :
    ∃ i : Fin 5, ∀ g : Equiv.Perm (Fin 5),
      coreRepresentation (Fin 5) g v = v ↔ g i = i := by
  have hh : ∀ v : core (Fin 5), v ≠ 0 → FiveGeometry.form v = 0 →
      ∃ i : Fin 5, ∀ g : Equiv.Perm (Fin 5),
        coreRepresentation (Fin 5) g v = v ↔ g i = i := by
    decide +kernel
  exact hh v hv hs

/-- A marked normal A5 component controls the full Sylow-fixed point radical,
including the outer action. The precise kernel and relative normality are retained. -/
theorem overgroup_point_baumann
    (K U : Subgroup H) [K.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (q : K →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 K)
    (e : U ≃* Multiplicative (core (Fin 5)))
    (he : ∀ (k : K) (u : U), (e (MulAut.conjNormal k.val u)).toAdd =
      coreRepresentation (Fin 5) (q k).val (e u).toAdd)
    (hquot : IsPGroup 2 (H ⧸ K))
    (hcore : pCore 2 H ≤ centralizer (U : Set H))
    (w : U) (hw : w ≠ 1) (S : Sylow 2 K)
    (hSw : (S : Subgroup K).map K.subtype ≤ centralizer ({w.val} : Set H)) :
    let R := (centralizer ({w.val} : Set H)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 H) ∧
      baumann R = baumann (pCore 2 H) ∧ (baumann R).Normal := by
  let σ := Representation.NormalElementaryQuotient.originalAction U
  let a0 : Additive U ≃+ core (Fin 5) :=
    e.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let a : Additive U ≃ₗ[ZMod 2] core (Fin 5) := { a0 with map_smul' := ZMod.map_smul a0 }
  let c := coreEquivNatural (Fin 5) (by decide)
  let E := a.trans c
  have ha (h : H) (u : Additive U) : a (σ h u) = (e (MulAut.conjNormal h u.toMul)).toAdd := by
    have hu : (σ h u).toMul = MulAut.conjNormal h u.toMul :=
      Subtype.ext (Representation.NormalElementaryQuotient.originalAction_apply U h u)
    change (e (σ h u).toMul).toAdd = _
    rw [hu]
  have hE (k : K) (u : Additive U) :
      E (σ k.val u) = naturalRepresentation (Fin 5) (q k).val (E u) := by
    change c (a (σ k.val u)) = _
    rw [ha,he,coreEquivNatural_equivariant]
    rfl
  obtain ⟨f,hf,hfK⟩ := Representation.OrthogonalFourMinus.FivePoint.exists_ambient_permutation_of_cover
    σ K q hq E hE
  have heF (h : H) (u : U) : (e (MulAut.conjNormal h u)).toAdd =
      coreRepresentation (Fin 5) (f h) (e u).toAdd := by
    apply c.injective
    rw [coreEquivNatural_equivariant]
    exact (congrArg c (ha h (Additive.ofMul u))).symm.trans (hf h (Additive.ofMul u))
  have hfix (h : H) (u : U) :
      coreRepresentation (Fin 5) (f h) (e u).toAdd = (e u).toAdd ↔ h*u.val=u.val*h := by
    rw [←heF,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    exact mul_inv_eq_iff_eq_mul
  have hker : f.ker = centralizer (U : Set H) := by
    ext h
    constructor
    · intro hh u hu
      have hh' : f h = 1 := hh
      have hhf : coreRepresentation (Fin 5) (f h) (e ⟨u,hu⟩).toAdd = (e ⟨u,hu⟩).toAdd := by
        rw [hh',map_one]; rfl
      exact ((hfix h ⟨u,hu⟩).mp hhf).symm
    · intro hh
      change f h = 1
      apply naturalRepresentation_injective (Fin 5) (by decide)
      apply LinearMap.ext
      intro v
      obtain ⟨u,rfl⟩ := E.surjective v
      rw [←hf,map_one,Module.End.one_apply]
      congr 1
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [Representation.NormalElementaryQuotient.originalAction_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (hh u.toMul.val u.toMul.property).symm
  have hKf : K.map f = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      rw [hfK ⟨k,hk⟩]
      exact (q ⟨k,hk⟩).property
    · intro b hb
      obtain ⟨k,hk⟩ := hq ⟨b,hb⟩
      exact ⟨k.val,k.property,(hfK k).trans (congrArg Subtype.val hk)⟩
  have hC : centralizer (U : Set H) = pCore 2 H := by
    have hp : IsPGroup 2 f.ker := f.isPGroup_ker_of_card_image_eq_core_quotient K hquot (by
      rw [hKf,←hk,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv])
    exact le_antisymm (le_sSup ⟨inferInstance,hker ▸ hp⟩) hcore
  let v := (e w).toAdd
  have hv : v ≠ 0 := fun hh => hw (e.injective (hh.trans e.map_one.symm))
  let S₀ := S.mapSurjective hq
  have hs : FiveGeometry.form v = 0 := FiveSylowSingular.fixed_singular S₀ v (by
    intro b hb
    obtain ⟨k,hk,rfl⟩ := (show b ∈ (S : Subgroup K).map q from hb)
    change coreRepresentation (Fin 5) (q k).val v = v
    rw [←hfK]
    exact (hfix k.val w).mpr (mem_centralizer_singleton_iff.mp
      (hSw (mem_map_of_mem K.subtype hk))))
  obtain ⟨i,hi⟩ := singular_point_stabilizer v hv hs
  let P := centralizer ({w.val} : Set H)
  let R := P.pCoreIn 2
  have hB : alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 5)) i ≤ P.map f := by
    intro b hb
    obtain ⟨k,hk⟩ := hq ⟨b,hb.1⟩
    have heqb : f k.val = b := (hfK k).trans (congrArg Subtype.val hk)
    refine ⟨k.val,?_,heqb⟩
    exact mem_centralizer_singleton_iff.mpr ((hfix k.val w).mp
      (by rw [heqb]; exact (hi b).mpr hb.2))
  have heven : R.map f ≤ alternatingGroup (Fin 5) :=
    AlternatingFiveBorel.even_point_stabilizer_normalizes_twoSubgroup _
      ((isPGroup_pCoreIn 2 P).map f) i
      (hB.trans ((map_mono (P.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))).trans
          (R.le_normalizer_map f)))
  have hQP : pCore 2 H ≤ P := by
    rw [←hC]
    exact fun h hh => mem_centralizer_singleton_iff.mpr (hh w.val w.property).symm
  have hQR : pCore 2 H ≤ R :=
    le_pCoreIn_of_normalizes pCore_isPGroup hQP (by rw [normalizer_eq_top]; exact le_top)
  have hUR : U ≤ R :=
    (show U ≤ pCore 2 H from le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans hQR
  have hJ := Offenders.thompson_le_kernel_of_even_core_action (Or.inl rfl) U R hUR f hker e heF heven
  have hRC : pCore 2 H = R ⊓ centralizer (U : Set H) := by rw [hC,inf_eq_right.mpr hQR]
  have hb := lemma_B_2_10_centralizing U R hUR hQR hRC
    (by rw [thompsonJ_zero,←hker]; exact hJ)
  exact ⟨by simpa only [thompsonJ_zero] using hb.1,hb.2.1,hb.2.2.2⟩
end CFSG.Quasithin.ChapterB.AlternatingFivePoint
