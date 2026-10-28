module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FrattiniOrbit
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveGeometry
public import Theory.Representation.BinaryFiveOrbit

/-!
# Abelian closure in the original index-five branch

Under the selected Chapter 14 hypotheses, H/O₂(H) equal to D₁₀ or
Sz(2) forces U=⟨V^H⟩ to be abelian. If U were nonabelian, its Frattini
subgroup would be the original point of order two. The square form on
the literal Frattini quotient has a singular spanning orbit of length
five, and the opposite-vertex geometry gives an elementary subgroup
of U of index at most four. The binary pentagon calculation then makes
the square form, and hence its polar, zero, contradicting noncommutativity.

The proof keeps the entire quotient, including any fixed binary factor.
It supplies a local input to the recognition in Aschbacher–Smith
14.2.20(1), printed p.987; the global Ree/Tits recognition is separate.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open LocalBinary ChapterG.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The actual selected outside subgroup has abelian conjugate closure of
its original plane in the D₁₀ and Sz(2) quotient cases. -/
theorem source_index_five_closure_abelian
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hmodel : Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) :
    IsMulCommutative (conjugateSpanBy (localModule T M) H) := by
  by_contra hne
  let D : Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hpc,w,hw,hfix,hspan,hzero,hbne⟩ :=
    source_frattini_seed_orbit hG T hempty hM hu hmany hcard e H hH hne
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let ρ := frattiniRepresentation D h.U_isPGroup
  let hφ := frattini_card_two D h
    (plane_centralInvolutions_card T M hM.1.2 hcard e) hne
  let Q := SmallFrattini.quotientQuadraticForm h.U_isPGroup hφ
  let S := T.subtype hH.1.2
  have hi : S.index = 5 := by
    let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
    have hPi : P.index = S.index := (S : Subgroup H).index_map_eq
      (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']
        exact pCore_isPGroup.le_sylow_of_normal S)
    have hcount := (P : Subgroup (H ⧸ pCore 2 H)).index_mul_card
    have hPc := P.card_eq_multiplicity
    have hc : Nat.card (H ⧸ pCore 2 H) = 10 ∨ Nat.card (H ⧸ pCore 2 H) = 20 := by
      rcases hmodel with hm | hm
      · obtain ⟨f⟩ := hm
        exact Or.inl ((Nat.card_congr f.toEquiv).trans (by simpa using (DihedralGroup.nat_card (n := 5))))
      · obtain ⟨f⟩ := hm
        exact Or.inr ((Nat.card_congr f.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card)
    rcases hc with hc | hc
    all_goals rw [hc] at hPc hcount
    · norm_num [show (Nat.factorization 10) 2 = 1 from by decide +kernel] at hPc
      rw [hPc,hPi] at hcount
      omega
    · norm_num [show (Nat.factorization 20) 2 = 2 from by decide +kernel] at hPc
      rw [hPc,hPi] at hcount
      omega
  have hfixed (s : S) : ρ s (Additive.ofMul w) = Additive.ofMul w := by
    change Additive.ofMul (frattiniActor D (s : H) w) = Additive.ofMul w
    apply congrArg Additive.ofMul
    apply hfix
    exact (hM.1.2.trans (show M ≤ normalizer (localModule T M : Set G) from
      le_normalizer_conjugateSpanBy _ _)) s.property
  have hinv (g : H) (x : Additive (D.U ⧸ frattini D.U)) : Q (ρ g x) = Q x := by
    exact SmallFrattini.quotientQuadraticForm_invariant h.U_isPGroup hφ (closureActor D g) x.toMul
  obtain ⟨A,hAU,hA,hindex⟩ :=
    source_index_five_elementary_subgroup hG T hempty hM hu hmany hcard e H hH hmodel hne
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 (A.subgroupOf D.U) := IsElementaryAbelian.subgroupOf hAU
  obtain ⟨E,hE,_,hcodim⟩ := SmallFrattini.exists_totallySingular_of_index
    h.U_isPGroup hφ (A.subgroupOf D.U) 2 hindex
  have hQ : Q = 0 := BinaryPentagon.eq_zero_of_index_five_orbit
    ρ S hi (Additive.ofMul w) hfixed hspan Q hzero hinv E hE hcodim
  apply hbne
  rw [←SmallFrattini.quotientQuadraticForm_polar]
  change Q.polarBilin = 0
  rw [hQ]
  ext x y
  simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]

end CFSG.Quasithin.Chapter14.Section02
