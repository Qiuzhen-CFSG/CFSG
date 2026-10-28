module
public import Theory.Representation.BinaryPermutation.SevenTriangle.PointGeneration
public import Theory.Representation.BinaryPermutation.PointStabilizerRank.Seven
public import Theory.Representation.BinaryConjugationSection.NaturalGeneration
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.GroupAction.FourPerfectOrbit
public import Theory.GroupTheory.PrimeOrderClosure
public import Theory.GroupTheory.PrimeIndexCentralizer
public import Theory.Quasithin.TwoKernelSubgroupRank

/-!
# Plane-normalizer generation in the seven-letter natural section

For a literal central binary quotient, cubic point stabilizers lift to the
centralizer of the original plane. Its three-rank bound excludes vectors
of weights four and six. A two-perfect actor moving the entire seed makes
all three nonzero seed vectors have weight two. Triangle-plane generation
then lifts through the same kernel to the whole numerator.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
14.7.37(3), printed pp.1059–1060. This formulation retains the actual
quotient map, the point and seed subgroups, and the centralizer rank bound.
-/

public noncomputable section
namespace Representation.BinaryConjugationSection
open Subgroup BinaryPermutation BinaryPermutation.SevenParabolic
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {H U Z : Subgroup G}
  (π : H →* Equiv.Perm (Fin 7))
  (c : BinaryConjugationSection H U Z (action.comp π))

omit [Finite G] in
private theorem seven_cubic_fixes_lift (hZ : Nat.card Z = 2)
    (hHZ : H ≤ centralizer (Z : Set G)) (a : H) (ha : a ^ 3 = 1)
    (v : U) (hf : action (π a) (c.coordinates v).toAdd = (c.coordinates v).toAdd) :
    (a : G) * v * (a : G)⁻¹ = v := by
  let v' : U := ⟨a * v * (a : G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized a.property) v).mp v.property⟩
  have he : c.coordinates v' = c.coordinates v := c.equivariant a v |>.trans hf
  have hm : ((v' * v⁻¹ : U) : G) ∈ Z := (c.coordinates_eq_one_iff _).mp (by
    rw [map_mul,map_inv,he,mul_inv_cancel])
  let z := (a : G) * v * (a : G)⁻¹ * (v : G)⁻¹
  have hz : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hm⟩ : Z))
    rw [hZ] at hh
    exact congrArg Subtype.val hh
  let f : MulAut G := MulAut.conj (a : G)
  have hfv : f v = z * v := by dsimp [f,z]; group
  have hfz : f z = z := by
    change (a : G) * z * (a : G)⁻¹ = z
    rw [← mem_centralizer_iff.mp (hHZ a.property) z hm,mul_inv_cancel_right]
  have htwo : f (f v) = v := by
    rw [hfv,map_mul,hfz,hfv,←mul_assoc,←pow_two,hz,one_mul]
  have hthree : f (f (f v)) = v := by
    have hh : f ^ 3 = 1 := by
      change MulAut.conj (a : G) ^ 3 = 1
      rw [←map_pow,show (a : G)^3 = 1 from congrArg Subtype.val ha,map_one]
    have hh' := congrArg (fun g : MulAut G => g (v : G)) hh
    simpa only [pow_succ,pow_zero,mul_one,MulAut.mul_apply,MulAut.one_apply] using hh'
  change f v = v
  simpa only [htwo] using hthree

/-- Three-rank of a point stabilizer lifts through the literal central binary kernel. -/
theorem seven_point_rank_le (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (P : Subgroup G) (hZP : Z ≤ P) (hi : Z.relIndex P = 2)
    (hZ : Nat.card Z = 2) (hHZ : H ≤ centralizer (Z : Set G))
    (v : U) (hv : (v : G) ∈ P) (hvZ : (v : G) ∉ Z) :
    primeRank 3 (BinaryNaturalDual.VectorStabilizers.representationStabilizer action
      (c.coordinates v).toAdd) ≤ primeRank 3 (centralizer (P : Set G)) := by
  let S := BinaryNaturalDual.VectorStabilizers.representationStabilizer action (c.coordinates v).toAdd
  let R := S.comap π
  let D := closure {a : H | a ∈ R ∧ orderOf a = 3}
  have hDC : D ≤ (centralizer (P : Set G)).subgroupOf H := by
    apply (closure_le _).mpr
    intro a ha
    have hfix := seven_cubic_fixes_lift π c hZ hHZ a
      (ha.2 ▸ pow_orderOf_eq_one a) v ha.1
    have haC : (a : G) ∈ H ⊓ centralizer ({(v : G)} : Set G) :=
      ⟨a.property,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)⟩
    rw [inf_centralizer_eq_of_prime_index_supplement H Z P hZP Nat.prime_two hi hHZ v hv hvZ] at haC
    exact haC.2
  rw [←primeRank_comap_eq_of_isTwoGroup_ker 3 (by decide) π hπ hker S,
    ←primeRank_primeOrderClosure 3 R]
  exact (primeRank_congr 3 (D.equivMapOfInjective H.subtype H.subtype_injective)).le.trans
    (primeRank_mono 3 ((map_le_iff_le_comap).mpr hDC))

/-- A two-perfect subgroup moving the whole seed is transitive on its four-element quotient. -/
theorem seven_seed_orbit (B D : Subgroup G) (hBU : B ≤ U) (hZB : Z ≤ B)
    (hi : Z.relIndex B = 4) (hDH : D ≤ H) (hDN : D ≤ normalizer (B : Set G))
    (hD : IsPPerfect 2 D) (hmove : ⁅B,D⁆ = B) :
    ∀ u ∈ c.imageSpace B, u ≠ 0 → ∀ v ∈ c.imageSpace B, v ≠ 0 →
      ∃ a : D, action (π (inclusion hDH a)) u = v := by
  let E := c.imageSpace B
  let ρ := (action.comp π).comp (inclusion hDH)
  have hs (a : D) : ∀ v ∈ E, ρ a v ∈ E :=
    c.imageSpace_apply_mem B (inclusion hDH a) (hDN a.property)
  let σ := Representation.subrepresentation ρ E hs
  have hd : Module.finrank (ZMod 2) E = 2 := c.imageSpace_finrank_of_index B hBU 2 hi
  have hn : ∃ a, σ a ≠ 1 := by
    by_contra ht
    push Not at ht
    have hc : ⁅D,B⁆ ≤ Z := by
      apply commutator_le.mpr
      intro a ha b hb
      let u : U := ⟨b,hBU hb⟩
      have hu : (c.coordinates u).toAdd ∈ E := (c.mem_imageSpace_iff B _).mpr ⟨u,hb,rfl⟩
      have hf := congrArg Subtype.val (LinearMap.congr_fun (ht ⟨a,ha⟩) ⟨_,hu⟩)
      let v : U := ⟨a*b*a⁻¹,(mem_normalizer_iff.mp (c.normalized (hDH ha)) b).mp u.property⟩
      have he : c.coordinates v = c.coordinates u := (c.equivariant ⟨a,hDH ha⟩ u).trans hf
      exact (c.coordinates_eq_one_iff (v*u⁻¹)).mp (by rw [map_mul,map_inv,he,mul_inv_cancel])
    rw [commutator_comm,hmove] at hc
    have he : B = Z := le_antisymm hc hZB
    rw [he,relIndex_self] at hi
    omega
  intro u hu hu0 v hv hv0
  obtain ⟨a,ha⟩ := Representation.nonzero_orbit_of_twoPerfect_plane hD hd σ hn
    ⟨u,hu⟩ (fun he => hu0 (congrArg Subtype.val he))
    ⟨v,hv⟩ (fun he => hv0 (congrArg Subtype.val he))
  exact ⟨a,congrArg Subtype.val ha⟩

include c in
/-- The seven-letter natural action forces generation by the actual plane normalizer. -/
theorem seven_plane_normalizer_generates
    (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (B P D : Subgroup G) (hBU : B ≤ U) (hPB : P ≤ B) (hZP : Z ≤ P)
    (hZ : Nat.card Z = 2) (hP : Z.relIndex P = 2) (hB : Z.relIndex B = 4)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hDH : D ≤ H) (hDN : D ≤ normalizer (B : Set G))
    (hD : IsPPerfect 2 D) (hmove : ⁅B,D⁆ = B)
    (hr : primeRank 3 (centralizer (P : Set G)) ≤ 1) :
    conjugateSpanBy B (H ⊓ normalizer (P : Set G)) = U := by
  let C := H ⊓ normalizer (P : Set G)
  let S := conjugateSpanBy B C
  have hBS : B ≤ S := le_conjugateSpanBy _ _
  have hSU : S ≤ U := conjugateSpanBy_le hBU (inf_le_left.trans c.normalized)
  have hPZ : ¬ P ≤ Z := by
    intro hp
    have he : P = Z := le_antisymm hp hZP
    rw [he,relIndex_self] at hP
    omega
  obtain ⟨v,hv,hvZ⟩ := SetLike.not_le_iff_exists.mp hPZ
  let vU : U := ⟨v,hBU (hPB hv)⟩
  let u := (c.coordinates vU).toAdd
  have hu : u ∈ c.imageSpace B := (c.mem_imageSpace_iff B _).mpr ⟨vU,hPB hv,rfl⟩
  have hu0 : u ≠ 0 := fun he => hvZ ((c.coordinates_eq_one_iff vU).mp he)
  have hur := (seven_point_rank_le π c hπ hker P hZP hP hZ hHZ vU hv hvZ).trans hr
  have hweight : weight u = 2 := by
    have hcases : ∀ v : Fin 7 → ZMod 2, (∑ i,v i)=0 → v ≠ 0 →
        (Finset.univ.filter (fun i => v i ≠ 0)).card = 2 ∨
        (Finset.univ.filter (fun i => v i ≠ 0)).card = 4 ∨
        (Finset.univ.filter (fun i => v i ≠ 0)).card = 6 := by decide +kernel
    have hc := hcases u.val ((mem_core (Fin 7) u.val).mp u.property)
      (fun he => hu0 (Subtype.ext he))
    have haltr : primeRank 3 (BinaryNaturalDual.VectorStabilizers.representationStabilizer
        (alternatingCoreRepresentation (Fin 7)) u) ≤ 1 := by
      let f : BinaryNaturalDual.VectorStabilizers.representationStabilizer
          (alternatingCoreRepresentation (Fin 7)) u →*
          BinaryNaturalDual.VectorStabilizers.representationStabilizer action u := {
        toFun a := ⟨a.val.val,a.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
      exact (primeRank_le_of_injective 3 f (by intro a b he; exact Subtype.ext (Subtype.ext (congrArg (fun z : BinaryNaturalDual.VectorStabilizers.representationStabilizer action u => z.val) he)))).trans hur
    rcases hc with hc | hc | hc
    · exact hc
    · have := PointStabilizerRank.two_le_weight_four_stabilizer u hc; omega
    · have := PointStabilizerRank.two_le_weight_six_stabilizer u hc; omega
  have hw : ∀ w ∈ c.imageSpace B, w ≠ 0 → weight w = 2 := by
    intro w hw hw0
    obtain ⟨a,ha⟩ := seven_seed_orbit π c B D hBU (hZP.trans hPB) hB hDH hDN hD hmove u hu hu0 w hw hw0
    rw [←ha,weight_permute]
    exact hweight
  have htop : c.imageSpace S = ⊤ := by
    apply SevenTriangle.point_stabilizer_generates (c.imageSpace B) (c.imageSpace S)
      (c.imageSpace_finrank_of_index B hBU 2 hB) hw u hu hu0 (c.imageSpace_mono hBS)
    intro g hg w hw
    obtain ⟨a,rfl⟩ := hπ g
    have hpre : a ∈ (normalizer (P : Set G)).subgroupOf H := by
      have him : ∀ (y : G) (hy : y ∈ P), (c.coordinates ⟨a*y*(a:G)⁻¹,
          (mem_normalizer_iff.mp (c.normalized a.property) y).mp (hBU (hPB hy))⟩).toAdd ∈ c.imageSpace P := by
        intro y hy
        have hdim : Module.finrank (ZMod 2) (c.imageSpace P) = 1 := c.imageSpace_finrank_of_index P (hPB.trans hBU) 1 hP
        have huP : u ∈ c.imageSpace P := (c.mem_imageSpace_iff P _).mpr ⟨vU,hv,rfl⟩
        have he : c.imageSpace P = Submodule.span (ZMod 2) {u} :=
          (eq_span_singleton_of_mem_of_finrank_eq_one hdim huP hu0)
        have hy' : (c.coordinates ⟨y,hBU (hPB hy)⟩).toAdd ∈ c.imageSpace P :=
          (c.mem_imageSpace_iff P _).mpr ⟨⟨y,hBU (hPB hy)⟩,hy,rfl⟩
        rw [he] at hy'
        obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hy'
        rw [c.equivariant a ⟨y,hBU (hPB hy)⟩,←hr]
        change action (π a) (r • u) ∈ c.imageSpace P
        rw [map_smul,hg]
        exact (c.imageSpace P).smul_mem r huP
      have hforward : ∀ y ∈ P, (a : G)*y*(a : G)⁻¹ ∈ P := by
        intro y hy
        exact (c.coordinates_mem_imageSpace_iff_of_kernel_le P hZP _).mp (him y hy)
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hle : P.map (MulAut.conj (a : G)).toMonoidHom ≤ P := by
        rintro _ ⟨z,hz,rfl⟩
        exact hforward z hz
      exact eq_of_le_of_card_ge hle (by
        rw [card_map_of_injective (MulAut.conj (a : G)).injective])
    exact c.imageSpace_apply_mem S a
      (le_normalizer_conjugateSpanBy B C ⟨a.property,hpre⟩) w hw
  exact le_antisymm hSU ((c.le_sup_kernel_of_image_top S htop).trans
    (sup_le le_rfl ((hZP.trans hPB).trans hBS)))
end Representation.BinaryConjugationSection
