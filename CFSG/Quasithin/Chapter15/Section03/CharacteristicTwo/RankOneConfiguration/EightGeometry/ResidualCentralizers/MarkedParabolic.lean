module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic.Marking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic.Residuals
public import Theory.Representation.BinaryPermutation.EightSylowFixed
public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic

/-!
# The marked end-node parabolic and its residuals

The local plane calculation produces a nonzero Sylow-fixed natural vector.
Its four-block stabilizer determines the compatible marking of C_L(Z_S)
and its Sylow extension. Pullback through the component quotient supplies
the binary two-plane parabolic and maximality. The separate two/three-order
argument then compares the two distinct residuals, including the two-group
kernel.

The final assembly discharges the two concrete model facts using the
Sylow-fixed-vector stabilizer theorem and the marked exceptional A₈ ≃ GL₄(2)
equivalence. Its remaining inputs are the independently supplied local
recognition, natural action, fixed-line and preliminary plane facts.
The separate identification L = O^{3′}(C_G(Z₁)) is used by the parent
assembly to identify the global residual centralizer in 15.3.32(4).

Source: Aschbacher–Smith, 15.3.32(4), printed pp.1132–1133.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
variable {G : Type*} [Group G] [Finite G]

/-- All local conclusions follow from the two independent concrete geometric facts. -/
theorem exists_marked_parabolic_of_model_facts (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S)
    (m : Parabolics.MiddleNodePermutationMarking d I c.L)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card d.ZS = 4)
    (hfirst : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (hsecond : Nat.card (d.ZS ⊓ d.V₂ : Subgroup G) = 2)
    (hinter : d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂)
    (hgeometry : ∀ (Q : Sylow 2 (Equiv.Perm (Fin 8)))
      (v : BinaryPermutation.natural (Fin 8)), v ≠ 0 →
      (∀ g ∈ (Q : Subgroup (Equiv.Perm (Fin 8))),
        BinaryPermutation.naturalRepresentation (Fin 8) g v = v) →
      ∃ r : Equiv.Perm (Fin 8), ∀ g : Equiv.Perm (Fin 8),
        BinaryPermutation.naturalRepresentation (Fin 8) g v = v ↔
          r * g * r⁻¹ ∈ fourStabilizer)
    (j : alternatingGroup (Fin 8) ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (W : Submodule (ZMod 2) (Fin 4 → ZMod 2)) (hd : Module.finrank (ZMod 2) W = 2)
    (hj : (BinaryLinear.parabolic W).comap j.toMonoidHom =
      fourStabilizer.subgroupOf (alternatingGroup (Fin 8)))
    (hmax : IsCoatom (fourStabilizer.subgroupOf (alternatingGroup (Fin 8)))) :
    ∃ b : CompatibleStarMarking d I (d.componentModule I c.L) a,
      IsCoatom ((c.L ⊓ centralizer (d.ZS : Set G)).subgroupOf c.L) ∧
      d.S ⊓ c.L ≤ c.L ⊓ centralizer (d.ZS : Set G) ∧
      d.S ≤ normalizer ((c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G) : Set G) ∧
      Nonempty (EndNodeParabolicModel c.L (c.L ⊓ centralizer (d.ZS : Set G))) ∧
      (d.starImage I c.L).map b.equiv.toMonoidHom = alternatingGroup (Fin 8) ∧
      (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map b.equiv.toMonoidHom =
        fourStabilizer ⊓ alternatingGroup (Fin 8) ∧
      (d.starImage I ((c.L ⊓ centralizer (d.ZS : Set G)) ⊔ d.S)).map
        b.equiv.toMonoidHom = fourStabilizer ∧
      RankOne.threeResidualIn (c.L ⊓ centralizer (d.ZS : Set G)) =
        (pResidual 2 (c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G)).map
          (c.L ⊓ centralizer (d.ZS : Set G)).subtype := by
  obtain ⟨b, hL, hK, hKS⟩ := exists_marking_of_fixedVector_geometry d c hn hjoin m a P hP hC
    hfixed hcard hfirst hsecond hinter hgeometry
  refine ⟨b, centralizer_isCoatom_of_marked_image d c hn P hP hC b.equiv hL hK hmax,
    sylow_intersection_le_centralizer d c.L,
    sylow_normalizes_centralizer d c hn (hjoin ▸ le_sup_right),
    ⟨endNodeModelOfMarkedImage d c hn P hP hC b.equiv hL hK j W hd hj⟩,
    hL, hK, hKS, ?_⟩
  exact residual_eq_of_fourBlock_image d c P hP hC b.equiv _
    (inf_le_left.trans (component_le c)) (by rw [hK]; exact inf_le_left)

/-- The centralizer `K = C_L(Z_S)` is the maximal two-plane parabolic over
`S ∩ L`, normalized by `S`. The compatible marking takes `K*` and `(KS)*`
to the even and full unordered four-block stabilizers, respectively, and
the two distinct residuals of `K` agree. All concrete model facts are proved;
only the independently supplied local inputs to 15.3.32(4) remain hypotheses. -/
theorem exists_marked_parabolic (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S)
    (m : Parabolics.MiddleNodePermutationMarking d I c.L)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card d.ZS = 4)
    (hfirst : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (hsecond : Nat.card (d.ZS ⊓ d.V₂ : Subgroup G) = 2)
    (hinter : d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂) :
    ∃ b : CompatibleStarMarking d I (d.componentModule I c.L) a,
      IsCoatom ((c.L ⊓ centralizer (d.ZS : Set G)).subgroupOf c.L) ∧
      d.S ⊓ c.L ≤ c.L ⊓ centralizer (d.ZS : Set G) ∧
      d.S ≤ normalizer ((c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G) : Set G) ∧
      Nonempty (EndNodeParabolicModel c.L (c.L ⊓ centralizer (d.ZS : Set G))) ∧
      (d.starImage I c.L).map b.equiv.toMonoidHom = alternatingGroup (Fin 8) ∧
      (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map b.equiv.toMonoidHom =
        fourStabilizer ⊓ alternatingGroup (Fin 8) ∧
      (d.starImage I ((c.L ⊓ centralizer (d.ZS : Set G)) ⊔ d.S)).map
        b.equiv.toMonoidHom = fourStabilizer ∧
      RankOne.threeResidualIn (c.L ⊓ centralizer (d.ZS : Set G)) =
        (pResidual 2 (c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G)).map
          (c.L ⊓ centralizer (d.ZS : Set G)).subtype := by
  obtain ⟨j, W, hd, hj, hmax⟩ :=
    Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.exists_model
  exact exists_marked_parabolic_of_model_facts d c hn hjoin m a P hP hC
    hfixed hcard hfirst hsecond hinter
    BinaryPermutation.EightSylowFixed.exists_conjugate_stabilizer j W hd hj hmax

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
end
