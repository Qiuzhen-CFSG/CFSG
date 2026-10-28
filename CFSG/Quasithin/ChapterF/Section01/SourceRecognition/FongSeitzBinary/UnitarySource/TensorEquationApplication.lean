module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorReflectionApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorSmallBruhat
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.QuotientData

/-!
# Complete U₄ source equations and FourData on the same marked quotient

Start with the original quadratic actor profile: both actual quotient maps,
the radical and index clauses, and the two remainder containments. Reuse
the constructed Hermitian coordinates, scalar torus and normalized A/C
reflection. The second Cartan and smaller Bruhat computations now supply
every relation of FourPresentation. A common Weyl section gives the
involution and dihedral laws, and the actual positive roots generate U.
Thus every FourData field is proved, including whole-quotient generation.

The general marking covers the geometric quotient as well as the original
SourceQuotient. The original specialization retains the literal Q.q-image
of S. Both orientations and q=2 and q=4 are included. The comparison
application constructs the full model equivalence and marked endpoints.

These results discharge the U₄ coordinate/presentation obligation at the
original quadratic profile. The earlier profile/cover and exhaustive row
selection still belong to qt-dgs85-quadrangle-structure and
qt-dgs85-split-quotient-recognition; U₅ source reconstruction belongs to
qt-dgs85-unitary-five-source-recognition. No earlier premise is removed.
Source: Fong--Seitz I (6A)(b), pp.37--38; II (8B), pp.201--202,
especially (8.7)--(8.9); DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
open Theory.PSL2.SemilinearCoverage
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
section Marked
variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (si : RootReflection Q split i) (sj : RootReflection Q split j)
  (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,F))
  (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) j
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
  (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include hVj sj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- Normalize the same tensor intertwiner to the actual second reflection,
using the common source Cartan and the trace commutator. -/
theorem marked_quadratic_tensor_reflection_realization :
    let μ := markedLinearLocalMarking Q mark h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (Space n) ≃* simpleRemainder Q split i),
      let l := fieldRelabelledActor Q split i hVi μ si n f
      let v : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) →* X ⧸ Q.D :=
        (simpleRemainder Q split i).subtype.comp e.toMonoidHom
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      (∀ (g : SL(2,Field n)) (p : Space n), l g * (e (.ofAdd p) : X ⧸ Q.D) *
        (l g)⁻¹ = e (.ofAdd (action n g p))) ∧
      (∀ a : Field n, (sj.val : X ⧸ Q.D) * r.A (.ofAdd a) * sj.val = r.C (.ofAdd a)) ∧
      (∀ a : Field n, (sj.val : X ⧸ Q.D) * r.C (.ofAdd a) * sj.val = r.A (.ofAdd a)) := by
  dsimp only
  let μ := markedLinearLocalMarking Q mark h split i hVi fi hfi hki
  obtain ⟨f,e,he,hA,hBroot,hC,hD,hfix⟩ := marked_quadratic_tensor_roots Q mark h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  have hF : Nat.card F = (2^n)^2 := by rw [hfields,hk]
  obtain ⟨_,_,hcard,_⟩ := marked_four_actor_cartan_cards Q mark h split
    hm j i hij.symm hVj hVi fj fi hfj hfi hkj hki n (NeZero.pos n) hk hF helem
  let hc := MarkedLocal.parabolic_core_selfCentralizing Q mark h i
  let l := fieldRelabelledActor Q split i hVi μ si n f
  let v : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) →* X ⧸ Q.D :=
        (simpleRemainder Q split i).subtype.comp e.toMonoidHom
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  let torus := tensorCartan Q split i hVi μ si n f e he hc hcard
  let scalar := tensorScalar Q split i hVi μ si n f e he hc hcard
  have hcl := tensorScalar_commute Q split i hVi μ si n f e he hc hcard
  have hscalar := tensorScalar_conjugation Q split i hVi μ si n f e he hc hcard
  have htorus := tensorCartan_range Q split i hVi μ si n f e he hc hcard
  have hl : Function.Injective l :=
    (GTwoSource.alignedPinningHom_injective Q split i hVi μ si).comp (Atlas.fieldEquivSL 2 f.symm).injective
  have hAi : Function.Injective r.A := hl.comp (SpecialLinearGroup.upperUnipotentHom_injective (Field n))
  let μj := markedLinearLocalMarking Q mark h split j hVj fj hfj hkj
  have ht2 : (sj.val : X ⧸ Q.D) * sj.val = 1 := by
    rw [←GTwoSource.alignedPinningHom_weyl Q split j hVj μj sj,←map_mul,weyl_sq,map_one]
  obtain ⟨c,hc0,hAC,hCA⟩ := secondReflection_AC_fixedScalar Q split i j (conjugation n) (conjugation_involutive n)
    r torus hBroot htorus.le
    (FourCartan.hom_B (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v he hscalar)
    hA hC hAi
    (FourCartan.hom_A (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v)
    (FourCartan.hom_C (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v he hscalar)
    sj (FourTensor.relations (Field n) (conjugation n) (conjugation_involutive n) l v he)
    (tensor_D_injective Q split n i l e) ht2
  let cfixed : fixedField n := c
  let cunit : (fixedField n)ˣ := Units.mk0 cfixed hc0
  let e' := (FourTensor.scale (Field n) (conjugation n) (conjugation_involutive n) cunit).trans e
  have he' (g : SL(2,Field n)) (p : Space n) :
      l g * (e' (.ofAdd p) : X ⧸ Q.D) * (l g)⁻¹ = e' (.ofAdd (action n g p)) := by
    change l g * (e (.ofAdd (cfixed • p)) : X ⧸ Q.D) * (l g)⁻¹ = e (.ofAdd (cfixed • action n g p))
    rw [he,map_smul]
  have hscaled (a : Field n) :
      (e' (.ofAdd (FourTensor.offDiagonal (Field n) (conjugation n) (conjugation_involutive n) a)) : X ⧸ Q.D) =
        r.C (.ofAdd ((c : Field n)*a)) := by
    exact congrArg (fun p : FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n) =>
      (e (.ofAdd p) : X ⧸ Q.D))
      (FourTensor.scale_off (Field n) (conjugation n) (conjugation_involutive n) cunit a)
  have htinv : (sj.val : X ⧸ Q.D)⁻¹ = sj.val := inv_eq_of_mul_eq_one_right ht2
  refine ⟨f,e',he',?_,?_⟩
  · intro a
    change (sj.val : X ⧸ Q.D) * r.A (.ofAdd a) * sj.val = _
    exact (htinv ▸ hAC a).trans (hscaled a).symm
  · intro a
    change (sj.val : X ⧸ Q.D) * (e' (.ofAdd (FourTensor.offDiagonal (Field n) (conjugation n) (conjugation_involutive n) a)) : X ⧸ Q.D) * sj.val = r.A (.ofAdd a)
    rw [hscaled]
    have hcE : (c : Field n) ≠ 0 := fun hh => hc0 (Subtype.ext hh)
    simpa only [htinv,←mul_assoc,inv_mul_cancel₀ hcE,one_mul] using hCA ((c : Field n)*a)


include hVj sj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
theorem marked_quadratic_tensor_equations
    (hst : ((si.val : X ⧸ Q.D)*sj.val)^4=1) :
    let μ := markedLinearLocalMarking Q mark h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (Space n) ≃* simpleRemainder Q split i)
      (t : FourWeyl.torusParameters (Field n) (conjugation n) →* X ⧸ Q.D),
      let l := fieldRelabelledActor Q split i hVi μ si n f
      let v : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) →* X ⧸ Q.D :=
        (simpleRemainder Q split i).subtype.comp e.toMonoidHom
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      (FourPresentation.parameters (Field n) (conjugation n) (conjugation_involutive n)).Satisfies
        (Presentation.Generator.ofMaps r t (si.val : X ⧸ Q.D) (sj.val : X ⧸ Q.D)) ∧
      r.generated = split.U ∧ t.range = Q.tits.B ⊓ Q.tits.N ∧
      (∀ x ∈ split.U, ∃ a d c b, x = r.word a d c b) := by
  dsimp only
  let μ := markedLinearLocalMarking Q mark h split i hVi fi hfi hki
  obtain ⟨f,e,he,htA,htC⟩ := marked_quadratic_tensor_reflection_realization Q mark h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  obtain ⟨_,_,_,_,hrj,_⟩ := QuadrangleStructure.marked_quadratic_linear_sixA Q mark h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne
  have hsmall : Nat.card (simpleRoot Q split j) = 2^n := hrj.trans hk
  have hA := fieldRelabelledActor_root_range Q split i hVi μ si n f
  have hs := fieldRelabelledActor_weyl Q split i hVi μ si n f
  have hBroot := tensor_B_range Q split n i j hij hm hVi hVj si _ e he hA hs hsmall
  have hfix := tensor_smallActor_centralizes_D Q split n i j hij hm hVi hVj si _ e he hA hs hsmall
  have hF : Nat.card F = (2^n)^2 := by rw [hfields,hk]
  obtain ⟨_,_,hcard,_⟩ := marked_four_actor_cartan_cards Q mark h split
    hm j i hij.symm hVj hVi fj fi hfj hfi hkj hki n (NeZero.pos n) hk hF helem
  let hc := MarkedLocal.parabolic_core_selfCentralizing Q mark h i
  let l := fieldRelabelledActor Q split i hVi μ si n f
  let v : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) →* X ⧸ Q.D :=
        (simpleRemainder Q split i).subtype.comp e.toMonoidHom
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  let t := tensorCartan Q split i hVi μ si n f e he hc hcard
  let scalar := tensorScalar Q split i hVi μ si n f e he hc hcard
  have hcl := tensorScalar_commute Q split i hVi μ si n f e he hc hcard
  have hscalar := tensorScalar_conjugation Q split i hVi μ si n f e he hc hcard
  have htorus := tensorCartan_range Q split i hVi μ si n f e he hc hcard
  have hwA := FourCartan.hom_A (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v
  have hwD := FourCartan.hom_D (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v he hscalar
  have hwC := FourCartan.hom_C (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v he hscalar
  have hwB := FourCartan.hom_B (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v he hscalar
  have hrel := FourTensor.relations (Field n) (conjugation n) (conjugation_involutive n) l v he
  have hl : Function.Injective l :=
    (GTwoSource.alignedPinningHom_injective Q split i hVi μ si).comp (Atlas.fieldEquivSL 2 f.symm).injective
  have hAi : Function.Injective r.A := hl.comp (SpecialLinearGroup.upperUnipotentHom_injective (Field n))
  let μj := markedLinearLocalMarking Q mark h split j hVj fj hfj hkj
  have hs2 := GTwoSource.sourceReflection_sq Q split i hVi μ si
  have ht2 := GTwoSource.sourceReflection_sq Q split j hVj μj sj
  have htD (d : fixedField n) : (sj.val : X ⧸ Q.D)*r.D (.ofAdd d)*sj.val = r.D (.ofAdd d) := by
    have hh := mem_centralizer_iff.mp (hfix sj.mem_rankOne) (r.D (.ofAdd d)) ⟨_,rfl⟩
    rw [←hh,mul_assoc,ht2,mul_one]
  have hth := secondReflection_cartan Q (conjugation n) (conjugation_involutive n) r t htorus
    hAi (tensor_C_injective Q split n i l e) hwA hwC sj.val ht2 htA htC
  have huniq (a : Field n) (d : fixedField n) (c a' : Field n) (d' : fixedField n) (c' : Field n)
      (hh : FourTensor.coreWord (conjugation n) r a d c = FourTensor.coreWord (conjugation n) r a' d' c') :
      a=a' ∧ c=c' := by
    have hu := FourTensor.tensor_coreWord_unique Q split (conjugation n) (conjugation_involutive n) i l e
      hA hAi a a' d d' c c' hh
    exact ⟨hu.1,hu.2.2⟩
  have htB (b : fixedField n) (hb : b ≠ 0) :
      (sj.val : X ⧸ Q.D)*r.B (.ofAdd b)*sj.val =
        r.B (.ofAdd b⁻¹)*t (FourBruhat.bTorus (Field n) (conjugation n) b hb)*sj.val*r.B (.ofAdd b⁻¹) := by
    obtain ⟨u,p,hword⟩ := exists_second_bruhat Q split (conjugation n) r t htorus j hVj μj sj
      hBroot (tensor_B_injective Q split n i l e) b hb
    obtain ⟨hu,hp⟩ := FourTensor.small_bruhat_coefficients (conjugation n) (conjugation_involutive n) r hrel
      (sj.val : X ⧸ Q.D) ht2 htA htC htD t hwA hwD hwC huniq b u hb p hword
    simpa only [hu,hp] using hword
  have hV : v.range = simpleRemainder Q split i := by
    change (((simpleRemainder Q split i).subtype).comp e.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,←MonoidHom.range_eq_map,range_subtype]
  have hgen : r.generated=split.U := by
    change (FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v).generated = _
    rw [FourTensor.generated_eq]
    change (l.comp (SpecialLinearGroup.upperUnipotentHom (Field n))).range ⊔ v.range = _
    change (l.comp (SpecialLinearGroup.upperUnipotentHom (Field n))).range = simpleRoot Q split i at hA
    rw [hA,hV]
    apply le_antisymm (sup_le (simpleRoot_le Q split i) inf_le_left)
    intro x hx
    have hm' : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
        (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]
      exact hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hm'
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  have hsB := FourCartan.weyl_B (Field n) (conjugation n) (conjugation_involutive n) l v he
  have hsC := FourCartan.weyl_C (Field n) (conjugation n) (conjugation_involutive n) l v he
  have hsD (d : fixedField n) : (si.val : X ⧸ Q.D)*r.D (.ofAdd d)*si.val = r.B (.ofAdd d) := by
    have hh := congrArg (fun x : X ⧸ Q.D => (si.val : X ⧸ Q.D)*x*si.val) (hsB d)
    rw [hs] at hh
    have hcancel : (si.val : X ⧸ Q.D)*((si.val : X ⧸ Q.D)*r.B (.ofAdd d)*si.val)*si.val = r.B (.ofAdd d) := by
      calc
        _ = ((si.val : X ⧸ Q.D)*si.val)*r.B (.ofAdd d)*((si.val : X ⧸ Q.D)*si.val) := by group
        _ = _ := by rw [hs2,one_mul,mul_one]
    exact hh.symm.trans hcancel
  refine ⟨f,e,t,?_,?_,htorus,?_⟩
  · intro x y heq
    cases heq <;> simp only [Presentation.a,Presentation.d,Presentation.c,Presentation.b,
      Presentation.h,Presentation.s,Presentation.t,map_one,map_mul,map_inv,map_pow,
      FreeGroup.lift_apply_of,Presentation.Generator.ofMaps]
    case ad a d => exact (hrel.AD a d).eq
    case cd c d => exact (hrel.CD c d).eq
    case bc b c => exact (hrel.BC b c).eq
    case ca c a => exact hrel.CA a.toAdd c.toAdd
    case bd b d =>
      change r.B b*r.D d = r.D d*r.C 1*r.B b
      rw [map_one,mul_one]
      exact (hrel.BD b d).eq
    case ba b a => exact hrel.BA a.toAdd b.toAdd
    case ha p a => exact hwA p a.toAdd
    case hd p d => exact hwD p d.toAdd
    case hc p c => exact hwC p c.toAdd
    case hb p b => exact hwB p b.toAdd
    case ss => exact hs2
    case tt => exact ht2
    case st => exact hst
    case sh p =>
      rw [←hs]
      exact FourCartan.weyl_hom (Field n) (conjugation n) l scalar hcl p
    case th p => exact hth p
    case sd d => exact hsD d.toAdd
    case sc c =>
      rw [←hs]
      exact hsC c.toAdd
    case sb b =>
      rw [←hs]
      exact hsB b.toAdd
    case ta a => exact htA a.toAdd
    case td d => exact htD d.toAdd
    case tc c => exact htC c.toAdd
    case sa a ha =>
      rw [←hs]
      exact FourCartan.weyl_A (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v a.toAdd (by simpa using ha)
    case tb b hb => exact htB b.toAdd (by intro hz; apply hb; exact hz)
  · exact hgen
  · intro x hx
    apply PositiveMaps.exists_word (FourPositive.Relations.collects (Field n) (conjugation n) (conjugation_involutive n) hrel)
    exact hgen.symm ▸ hx


include mark h hVi fi hfi hki hVj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- Every field of the full U₄ presentation is constructed on the same
original quotient. The Weyl section supplies the dihedral equation. -/
theorem marked_quadratic_fourData :
    ∃ d : UnitaryPresentation.FourData Q split j (conjugation n) (conjugation_involutive n),
      d.roots.generated = split.U ∧ d.cartan.range = Q.tits.B ⊓ Q.tits.N ∧
      (∀ x ∈ split.U, ∃ a z c b, x = d.roots.word a z c b) := by
  let w := quadrangleLifts Q split hm j
  have hi : 1-j=i := by omega
  let sref : RootReflection Q split i :=
    { val := w.s
      class_eq := by simpa only [hi] using w.s_class
      mem_rankOne := by
        change (w.s : X ⧸ Q.D) ∈ rootActor Q split i
        have hh := (quadrangleLifts_actor Q split hm j).1
        rw [hi] at hh
        exact hh }
  let tref : RootReflection Q split j :=
    { val := w.t
      class_eq := w.t_class
      mem_rankOne := (quadrangleLifts_actor Q split hm j).2 }
  have hst : ((sref.val : X ⧸ Q.D)*tref.val)^4=1 :=
    congrArg (fun x : Q.tits.N => (x : X ⧸ Q.D)) (quadrangleLifts_equations Q split hm j).2.2
  obtain ⟨f,e,t,heq,hgen,ht,hcol⟩ := marked_quadratic_tensor_equations Q mark h split
    hm i j hij hVi hVj sref tref fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk hst
  let μ := markedLinearLocalMarking Q mark h split i hVi fi hfi hki
  let l := fieldRelabelledActor Q split i hVi μ sref n f
  let v : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) →* X ⧸ Q.D :=
        (simpleRemainder Q split i).subtype.comp e.toMonoidHom
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  let d : UnitaryPresentation.FourData Q split j (conjugation n) (conjugation_involutive n) :=
    { roots := r
      cartan := t
      lifts := w
      equations := heq
      generate := marked_positive_fullGenerated Q split hm mark h j r t hgen
      positive_le := hgen.le
      cartan_le := ht.le }
  exact ⟨d,hgen,ht,hcol⟩

end Marked

variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (si : RootReflection Q split i) (sj : RootReflection Q split j)
  (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,F))
  (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) j
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
  (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include h hVi fi hfi hki hVj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- Full FourData and literal Q.q(S) collection on the original generated source. -/
theorem original_quadratic_fourData :
    ∃ d : UnitaryPresentation.FourData Q split j (conjugation n) (conjugation_involutive n),
      d.roots.generated = split.U ∧ d.cartan.range = Q.tits.B ⊓ Q.tits.N ∧
      (∀ x ∈ (S.subgroupOf (generated L S)).map Q.q, ∃ a z c b, x = d.roots.word a z c b) := by
  obtain ⟨d,hgen,ht,hcol⟩ := marked_quadratic_fourData Q (originalMarkedIso Q) h split
    hm i j hij hVi hVj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  refine ⟨d,hgen,ht,?_⟩
  intro x hx
  apply hcol x
  rwa [quotient_sourceS_image_eq_unipotent h Q split] at hx

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
