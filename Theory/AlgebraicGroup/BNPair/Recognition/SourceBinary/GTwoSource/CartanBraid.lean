module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.OrthogonalRoots

/-!
# Disjoint source Cartans and the general G₂ braid

If a source reflection inverts an element of the odd full Cartan H, the
square of that element lies in the corresponding R_i, hence so does the
element. The rank-one diagonal action is faithful on its simple root.
Orthogonal centralization of C by the long R then makes H_short and H_long
disjoint: transport centralization through C -> D -> F and use that faithful
action. This also proves injectivity of the constructed two-parameter torus.

The Weyl image of (rs)^6 is one. Both involutions invert this Cartan element,
placing it in the two disjoint factors, so the actual source lifts satisfy
(rs)^6 = 1. The existing EC commutation supplies the orthogonal centralizer.
All statements use the same quotient and include q=2 and q=4. The lower
positive equations and compatible common-field actions remain unproved.

Source: Fong--Seitz II §7, (7A), printed p.192, and (9.5)--(9.6), printed
p.212. The odd-Cartan argument here gives the braid directly from the
existing source pinnings. CartanWeights and WeightApplication consume it.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Inverting an odd Cartan element places it in the actual rank-one factor. -/
theorem cartan_inverted_mem_rankOne (i : Fin 2) (n : RootReflection Q split i)
    {z : X ⧸ Q.D} (hz : z ∈ Q.tits.B ⊓ Q.tits.N)
    (hinv : (n.val : X ⧸ Q.D)*z*(n.val : X ⧸ Q.D)⁻¹ = z⁻¹) :
    z ∈ rankOne Q split i := by
  have hc : (n.val : X ⧸ Q.D)*z⁻¹*(n.val : X ⧸ Q.D)⁻¹ = z := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      congrArg Inv.inv hinv
  have hz2 : z^2 ∈ rankOne Q split i := by
    have he : z^2 = (z*n.val*z⁻¹)*(n.val : X ⧸ Q.D)⁻¹ := by
      rw [pow_two, mul_assoc z (n.val : X ⧸ Q.D) z⁻¹, mul_assoc, hc]
    rw [he]
    exact (rankOne Q split i).mul_mem
      ((mem_normalizer_iff.mp (rankOne_torus_normalizes Q split i hz) n.val).mp n.mem_rankOne)
      ((rankOne Q split i).inv_mem n.mem_rankOne)
  let zH : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨z,hz⟩
  obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime
    (x := zH) (split.odd.of_dvd_right (orderOf_dvd_natCard zH))
  have he : (z^2)^k = z := congrArg Subtype.val hk
  rw [← he]
  exact (rankOne Q split i).pow_mem hz2 k

variable (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

include hK μ n

/-- The aligned rank-one torus acts faithfully on its own simple root. -/
theorem cartan_rankOne_eq_one_of_centralizes (i : Fin 2) {z : X ⧸ Q.D}
    (hzH : z ∈ Q.tits.B ⊓ Q.tits.N) (hzR : z ∈ rankOne Q split i)
    (hc : z ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D))) : z = 1 := by
  obtain ⟨a,rfl⟩ := exists_alignedTorus_of_mem Q split i (hK i) (μ i) (n i) hzH hzR
  have hx : alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd 1) ∈
      simpleRoot Q split i := by
    rw [← alignedSimpleParameter_range Q split i (hK i) (μ i) (n i)]
    exact ⟨_,rfl⟩
  have he := alignedTorus_root Q split i (hK i) (μ i) (n i) a 1
  rw [← mem_centralizer_iff.mp hc _ hx, mul_assoc, mul_inv_cancel, mul_one] at he
  have haa : (a : F)^2 = 1 := by
    have hh := Multiplicative.ofAdd.injective
      (alignedSimpleParameter_injective Q split i (hK i) (μ i) (n i) he)
    simpa only [mul_one] using hh.symm
  have ha : a = 1 := Units.ext (CharTwo.sq_injective (haa.trans (one_pow 2).symm))
  change alignedTorusHom Q split i (hK i) (μ i) (n i) a = 1
  rw [ha,map_one]

/-- Any element of H ∩ R_i is inverted by the specified i-reflection. -/
theorem reflection_inverts_cartan_rankOne (i : Fin 2) {z : X ⧸ Q.D}
    (hzH : z ∈ Q.tits.B ⊓ Q.tits.N) (hzR : z ∈ rankOne Q split i) :
    (n i).val*z*((n i).val : X ⧸ Q.D)⁻¹ = z⁻¹ := by
  obtain ⟨a,rfl⟩ := exists_alignedTorus_of_mem Q split i (hK i) (μ i) (n i) hzH hzR
  rw [reflection_alignedTorus]
  exact (alignedTorusHom Q split i (hK i) (μ i) (n i)).map_inv a

/-- The two actual Cartan factors are disjoint once the long rank-one group
centralizes the orthogonal middle short root. -/
theorem rankOne_cartan_disjoint
    (hc : rankOne Q split (1-short) ≤ centralizer
      (positiveCarrier Q split short 2 : Set (X ⧸ Q.D))) :
    Disjoint ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split short)
      ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split (1-short)) := by
  apply disjoint_def.mpr
  intro z hzs hzr
  let d := sourceBorelWeyl Q split hK μ n short split.abelian
  have hs : MulAut.conj d.s z = z⁻¹ :=
    reflection_inverts_cartan_rankOne Q split hK μ n short hzs.1 hzs.2
  have hr : MulAut.conj d.r z = z⁻¹ :=
    reflection_inverts_cartan_rankOne Q split hK μ n (1-short) hzr.1 hzr.2
  have hC (a : F) : Commute z (d.x 2 a) := by
    apply (mem_centralizer_iff.mp (hc hzr.2) _ ?_).symm
    rw [← alignedSourceRoots_range Q split hK μ n short 2]
    exact ⟨.ofAdd a,rfl⟩
  have hD (a : F) : Commute z (d.x 3 a) := by
    have hh := (hC a).map (MulAut.conj d.s).toMonoidHom
    change Commute (MulAut.conj d.s z) (d.s*d.x 2 a*d.s⁻¹) at hh
    rw [hs, sourceBorelWeyl_sC] at hh
    simpa only [inv_inv] using hh.inv_left
  have hF (a : F) : Commute z (d.x 5 a) := by
    have hh := (hD a).map (MulAut.conj d.r).toMonoidHom
    change Commute (MulAut.conj d.r z) (d.r*d.x 3 a*d.r⁻¹) at hh
    rw [hr, sourceBorelWeyl_rD] at hh
    simpa only [inv_inv] using hh.inv_left
  apply cartan_rankOne_eq_one_of_centralizes Q split hK μ n short hzs.1 hzs.2
  apply mem_centralizer_iff.mpr
  intro x hx
  change x ∈ positiveCarrier Q split short 5 at hx
  rw [← alignedSourceRoots_range Q split hK μ n short 5] at hx
  obtain ⟨a,rfl⟩ := hx
  exact (hF a.toAdd).symm.eq

omit hK μ n in
private theorem involutions_invert_product_powers {Y : Type*} [Group Y] {r s : Y}
    (hr : r^2 = 1) (hs : s^2 = 1) (k : ℕ) :
    MulAut.conj r ((r*s)^k) = ((r*s)^k)⁻¹ ∧
      MulAut.conj s ((r*s)^k) = ((r*s)^k)⁻¹ := by
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr)
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hR : MulAut.conj r (r*s) = (r*s)⁻¹ := by
    change r*(r*s)*r⁻¹ = _
    rw [← mul_assoc r r s, ← pow_two, hr, one_mul, mul_inv_rev, hs']
  have hS : MulAut.conj s (r*s) = (r*s)⁻¹ := by
    change s*(r*s)*s⁻¹ = _
    rw [← mul_assoc s r s, mul_assoc (s*r), mul_inv_cancel, mul_one, mul_inv_rev, hr', hs']
  constructor
  · rw [map_pow,hR,inv_pow]
  · rw [map_pow,hS,inv_pow]

/-- The actual source reflections satisfy the hexagonal braid, without a
restriction on q, once the long rank-one group centralizes its orthogonal root. -/
theorem source_reflections_braid (hm : rotationOrder Q = 6)
    (hc : rankOne Q split (1-short) ≤ centralizer
      (positiveCarrier Q split short 2 : Set (X ⧸ Q.D))) :
    (((n (1-short)).val : X ⧸ Q.D) * (n short).val)^6 = 1 := by
  let z : Q.tits.N := ((n (1-short)).val*(n short).val)^6
  have hz : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) z = 1 := by
    simp only [z,map_pow,map_mul,(n (1-short)).class_eq,(n short).class_eq]
    have he : orderOf (Q.simple (1-short)*Q.simple short) = 6 := by
      fin_cases short
      · simpa [rotationOrder] using (SemiconjBy.orderOf_eq (Q.simple 0) (show
          SemiconjBy (Q.simple 0) (Q.simple 1*Q.simple 0) (Q.simple 0*Q.simple 1) from
            (mul_assoc _ _ _).symm)).trans hm
      · exact hm
    rw [← he]
    exact pow_orderOf_eq_one _
  have hmem : (z : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := (QuotientGroup.eq_one_iff z).mp hz
  have hr : ((n (1-short)).val : X ⧸ Q.D)^2 = 1 := by
    simpa only [pow_two] using sourceReflection_sq Q split (1-short)
      (hK (1-short)) (μ (1-short)) (n (1-short))
  have hs : ((n short).val : X ⧸ Q.D)^2 = 1 := by
    simpa only [pow_two] using sourceReflection_sq Q split short (hK short) (μ short) (n short)
  obtain ⟨hrz,hsz⟩ := involutions_invert_product_powers hr hs 6
  exact disjoint_def.mp (rankOne_cartan_disjoint Q split hK μ n short hc)
    ⟨hmem,cartan_inverted_mem_rankOne Q split short (n short) hmem hsz⟩
    ⟨hmem,cartan_inverted_mem_rankOne Q split (1-short) (n (1-short)) hmem hrz⟩

/-- The two parameter coordinates of the constructed torus are faithful;
this uses the actual disjoint Cartan factors, including at q=2 and q=4. -/
theorem alignedPairTorus_injective (hH : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N))
    (hc : rankOne Q split (1-short) ≤ centralizer
      (positiveCarrier Q split short 2 : Set (X ⧸ Q.D))) :
    Function.Injective (alignedPairTorus Q split hK μ n short hH) := by
  apply (alignedPairTorus Q split hK μ n short hH).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  rintro ⟨l,m⟩ hp
  have he : alignedTorusHom Q split short (hK short) (μ short) (n short) l *
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (l*m) = 1 := hp
  have hs := alignedTorusHom_range Q split short (hK short) (μ short) (n short)
  have hr := alignedTorusHom_range Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
  have heq := eq_inv_of_mul_eq_one_left he
  have hh : alignedTorusHom Q split short (hK short) (μ short) (n short) l = 1 := by
    apply disjoint_def.mp (rankOne_cartan_disjoint Q split hK μ n short hc)
    · rw [← hs]
      exact ⟨l,rfl⟩
    · rw [heq, ← hr, ← map_inv]
      exact ⟨_,rfl⟩
  have hl : l = 1 := alignedTorusHom_injective Q split short (hK short) (μ short) (n short)
    (hh.trans (map_one _).symm)
  have hm : m = 1 := by
    rw [hh,one_mul,hl,one_mul] at he
    exact alignedTorusHom_injective Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
      (he.trans (map_one _).symm)
  exact mem_bot.mpr (Prod.ext hl hm)

/-- EC commutation already present in the lower positive input discharges the
braid clause of the literal Borel--Weyl presentation in every field. -/
theorem sourceBorelWeyl_braid (hH : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N))
    (hm : rotationOrder Q = 6)
    (hc : (alignedSourceRoots Q split hK μ n short).CommutingRelations) :
    let d := sourceBorelWeyl Q split hK μ n short hH
    (d.r*d.s)^6 = 1 :=
  source_reflections_braid Q split hK μ n short hm
    (aligned_long_centralizes Q split hK μ n short hm hc)


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
