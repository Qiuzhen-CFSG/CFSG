module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixFlags
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixKernel
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The two actual point-centralizer spans in the full six-letter core

Full-core coordinates carry ambient conjugate spans to linear orbit spans.
For the two marked nonzero plane vectors, their component centralizers have
exactly the even duad-stabilizer images. Their orbit spans are the two source
hyperplanes and together generate the original five-dimensional core.

Source: Aschbacher–Smith, 14.6.10(5), printed p.1030.
-/

@[expose] public noncomputable section
open Subgroup BinaryPermutation Module Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
variable {G : Type*} [Group G]

theorem mem_sourceImage (W : Subgroup G) (E : W ≃* Multiplicative (core (Fin 6)))
    (B : Subgroup G) (v : W) : (E v).toAdd ∈ sourceImage W E B ↔ v.val ∈ B := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hh : w = v := E.injective he
    exact hh ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem sourceImage_conjugateSpan (K W B A : Subgroup G)
    (E : W ≃* Multiplicative (core (Fin 6)))
    (f : K →* Equiv.Perm (Fin 6))
    (hKW : K ≤ normalizer (W : Set G)) (hAK : A ≤ K) (hBW : B ≤ W)
    (he : ∀ (k : K) (v : W),
      (E ⟨k.val*v.val*k.val⁻¹,
        le_normalizer_iff.mp hKW k k.property v v.property⟩).toAdd =
        coreRepresentation (Fin 6) (f k) (E v).toAdd) :
    sourceImage W E (conjugateSpanBy B A) =
      Homogeneous.orbitSpan (coreRepresentation (Fin 6)) ((A.subgroupOf K).map f)
        (sourceImage W E B) := by
  let P := Homogeneous.orbitSpan (coreRepresentation (Fin 6)) ((A.subgroupOf K).map f)
    (sourceImage W E B)
  let X : Subgroup W := P.toAddSubgroup.toSubgroup.comap E.toMonoidHom
  have hBX : B ≤ X.map W.subtype := by
    intro b hb
    refine ⟨⟨b,hBW hb⟩,?_,rfl⟩
    exact Homogeneous.le_orbitSpan _ _ _ ((mem_sourceImage W E B _).mpr hb)
  have hAX : A ≤ normalizer (X.map W.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    rintro a ha _ ⟨v,hv,rfl⟩
    let k : K := ⟨a,hAK ha⟩
    let w : W := ⟨a*v.val*a⁻¹,le_normalizer_iff.mp hKW k k.property v v.property⟩
    refine ⟨w,?_,rfl⟩
    change (E w).toAdd ∈ P
    rw [show (E w).toAdd = coreRepresentation (Fin 6) (f k) (E v).toAdd from he k v]
    exact (Homogeneous.orbitSpan_invariant _ _ _ (mem_map_of_mem f ha) _).2 hv
  have hspanX := conjugateSpanBy_le hBX hAX
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    obtain ⟨x,hx,hxw⟩ := hspanX hw
    have hxeq : x = w := Subtype.ext hxw
    exact hxeq ▸ hx
  · apply Homogeneous.orbitSpan_le
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨w,le_conjugateSpanBy B A hw,rfl⟩
    · apply le_subspaceStabilizer
      rintro _ ⟨a,ha,rfl⟩ v ⟨w,hw,rfl⟩
      refine ⟨⟨a.val*w.val*a.val⁻¹,
        le_normalizer_iff.mp hKW a a.property w w.property⟩,?_,?_⟩
      · exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy B A) a ha w hw
      · exact Multiplicative.toAdd.injective (he a w)
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry Representation.BinaryOffender
variable {G : Type*} [Group G] (K : Subgroup G)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (K : Set G)) (v : sourceModule K)
      (hv : n.val*v.val*n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (hfull : (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6))

include he
private theorem centralizes_point_iff (n : normalizer (K : Set G)) (p : sourceModule K) :
    n.val ∈ centralizer ({p.val} : Set G) ↔
      coreRepresentation (Fin 6) (f n) (E p).toAdd = (E p).toAdd := by
  have hnp : n.val*p.val*n.val⁻¹ ∈ sourceModule K :=
    (mem_normalizer_iff.mp
      (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K) n.property) p).mp p.property
  rw [←he n p hnp]
  constructor
  · intro hh
    congr 2
    apply Subtype.ext
    have hc := mem_centralizer_singleton_iff.mp hh
    change n.val*p.val*n.val⁻¹ = p.val
    rw [hc,mul_inv_cancel_right]
  · intro hh
    have hc := congrArg Subtype.val (E.injective (Multiplicative.toAdd.injective hh))
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc)

include hfull
private theorem source_point_image (p : sourceModule K) (D : Subgroup S)
    (hD : ∀ g : S, g ∈ D ↔
      coreRepresentation (Fin 6) g (E p).toAdd = (E p).toAdd ∧
        g ∈ alternatingGroup (Fin 6)) :
    ((K ⊓ centralizer ({p.val} : Set G)).subgroupOf (normalizer (K : Set G))).map f = D := by
  apply le_antisymm
  · rintro _ ⟨n,hn,rfl⟩
    exact (hD _).mpr ⟨(centralizes_point_iff K E f he n p).mp hn.2,
      hfull ▸ mem_map_of_mem f hn.1⟩
  · intro g hg
    obtain ⟨n,hn,hnf⟩ := hfull.symm ▸ ((hD g).mp hg).2
    refine ⟨n,⟨hn,?_⟩,hnf⟩
    exact (centralizes_point_iff K E f he n p).mpr (hnf.symm ▸ ((hD g).mp hg).1)

/-- The original component centralizer of the marked source point has exactly
its even duad-stabilizer image. -/
theorem source_z_centralizer_image (p : sourceModule K) (hp : (E p).toAdd = CoreCrossing.z) :
    ((K ⊓ centralizer ({p.val} : Set G)).subgroupOf (normalizer (K : Set G))).map f = L1 := by
  apply source_point_image K E f he hfull p L1
  intro g
  rw [hp]
  exact CoreCrossing.mem_L1_iff g

/-- The actual component point span has the full rank-four hyperplane image. -/
theorem source_z_span (B : Subgroup G) (hBW : B ≤ sourceModule K)
    (hB : sourceImage (sourceModule K) E B = CoreCrossing.plane)
    (p : sourceModule K) (hp : (E p).toAdd = CoreCrossing.z) :
    sourceImage (sourceModule K) E
      (conjugateSpanBy B (K ⊓ centralizer ({p.val} : Set G))) = CoreCrossing.hyperplane := by
  rw [sourceImage_conjugateSpan (normalizer (K : Set G)) (sourceModule K) B
    (K ⊓ centralizer ({p.val} : Set G)) E f
    (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
    (inf_le_left.trans K.le_normalizer) hBW (fun n v => he n v _),
    source_z_centralizer_image K E f he hfull p hp,hB,CoreCrossing.orbitSpan_eq_hyperplane]

omit he hfull in
private theorem core_fixes_w_iff (g : S) :
    g ∈ L1.map (MulAut.conj CoreCrossing.crossingRelabel).toMonoidHom ↔
      coreRepresentation (Fin 6) g CoreCrossing.w = CoreCrossing.w ∧
        g ∈ alternatingGroup (Fin 6) := by
  let r := CoreCrossing.crossingRelabel
  have hr : r ∈ alternatingGroup (Fin 6) := by decide
  have hz : coreRepresentation (Fin 6) r CoreCrossing.z = CoreCrossing.w := by decide
  have hzinv : coreRepresentation (Fin 6) r⁻¹ CoreCrossing.w = CoreCrossing.z := by decide
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨hf,halt⟩ := (CoreCrossing.mem_L1_iff a).mp ha
    constructor
    · change coreRepresentation (Fin 6) (r*a*r⁻¹) CoreCrossing.w = CoreCrossing.w
      rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hzinv,hf,hz]
    · exact (alternatingGroup (Fin 6)).mul_mem
        ((alternatingGroup (Fin 6)).mul_mem hr halt) ((alternatingGroup (Fin 6)).inv_mem hr)
  · rintro ⟨hf,halt⟩
    refine ⟨r⁻¹*g*r,(CoreCrossing.mem_L1_iff _).mpr ⟨?_,?_⟩,?_⟩
    · rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hz,hf,hzinv]
    · exact (alternatingGroup (Fin 6)).mul_mem
        ((alternatingGroup (Fin 6)).mul_mem ((alternatingGroup (Fin 6)).inv_mem hr) halt) hr
    · change r*(r⁻¹*g*r)*r⁻¹ = g
      group

/-- The other source-plane point gives the literal crossing hyperplane. -/
theorem source_w_span (B : Subgroup G) (hBW : B ≤ sourceModule K)
    (hB : sourceImage (sourceModule K) E B = CoreCrossing.plane)
    (p : sourceModule K) (hp : (E p).toAdd = CoreCrossing.w) :
    sourceImage (sourceModule K) E
      (conjugateSpanBy B (K ⊓ centralizer ({p.val} : Set G))) = CoreCrossing.crossingHyperplane := by
  have himage := source_point_image K E f he hfull p
    (L1.map (MulAut.conj CoreCrossing.crossingRelabel).toMonoidHom)
    (fun g => by rw [hp]; exact core_fixes_w_iff g)
  rw [sourceImage_conjugateSpan (normalizer (K : Set G)) (sourceModule K) B
    (K ⊓ centralizer ({p.val} : Set G)) E f
    (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
    (inf_le_left.trans K.le_normalizer) hBW (fun n v => he n v _),
    himage,hB,CoreCrossing.crossing_orbitSpan]
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G : Type*} [Group G]

private theorem sourceImage_mono (W : Subgroup G) (E : W ≃* Multiplicative (core (Fin 6)))
    {B D : Subgroup G} (h : B ≤ D) : sourceImage W E B ≤ sourceImage W E D := by
  rintro v ⟨w,hw,rfl⟩
  exact ⟨w,h hw,rfl⟩

/-- The two original point-centralizer spans generate the whole source core,
with both centralizers using the same ambient component and plane. -/
theorem source_two_point_spans_generate (K B : Subgroup G)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (K : Set G)) (v : sourceModule K)
      (hv : n.val*v.val*n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd = coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (hA : (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6))
    (hBW : B ≤ sourceModule K) (hB : sourceImage (sourceModule K) E B = CoreCrossing.plane)
    (z w : sourceModule K) (hz : (E z).toAdd = CoreCrossing.z) (hw : (E w).toAdd = CoreCrossing.w) :
    conjugateSpanBy B (K ⊓ centralizer ({z.val} : Set G)) ⊔
      conjugateSpanBy B (K ⊓ centralizer ({w.val} : Set G)) = sourceModule K := by
  let P := conjugateSpanBy B (K ⊓ centralizer ({z.val} : Set G))
  let Q := conjugateSpanBy B (K ⊓ centralizer ({w.val} : Set G))
  have hPW : P ≤ sourceModule K := conjugateSpanBy_le hBW
    (inf_le_left.trans (K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))))
  have hQW : Q ≤ sourceModule K := conjugateSpanBy_le hBW
    (inf_le_left.trans (K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))))
  have hP : sourceImage (sourceModule K) E P = CoreCrossing.hyperplane := source_z_span K E f he hA B hBW hB z hz
  have hQ : sourceImage (sourceModule K) E Q = CoreCrossing.crossingHyperplane := source_w_span K E f he hA B hBW hB w hw
  have htop : (⊤ : Submodule (ZMod 2) (core (Fin 6))) ≤ sourceImage (sourceModule K) E (P ⊔ Q) := by
    rw [←CoreCrossing.hyperplane_sup_crossing,←hP,←hQ]
    exact sup_le (sourceImage_mono _ E le_sup_left) (sourceImage_mono _ E le_sup_right)
  apply le_antisymm (sup_le hPW hQW)
  intro x hx
  exact (mem_sourceImage _ E (P ⊔ Q) ⟨x,hx⟩).mp (htop Submodule.mem_top)
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
