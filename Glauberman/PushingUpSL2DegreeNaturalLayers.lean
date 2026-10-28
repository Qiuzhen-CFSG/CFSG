module
public import Glauberman.PushingUpSL2DegreeParameters
public import Glauberman.PushingUpSL2DegreeNaturalCenter
public import Theory.GroupTheory.SubgroupTransport.GapFixedHalves
public import Theory.Representation.SL2.SharpSection

/-!
# Both natural factors of the original-degree Niles filtration

The full core center modulo all ambient fixed vectors and the second gap
factor carry the natural action for the same original SL₂ marking. The
other factors remain elementary and ambient central. For the upper factor,
the two fixed half intervals have index q, so the sharp Sylow fixed-space
recognition applies to the literal quotient of order q² with kernel O₂.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5,
pp.51--52. The later nonabelian structure and commutator conclusion are
not asserted here.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport Representation
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The literal full-center filtration, retaining the original action marking
on its upper natural factor and every ambient central factor. -/
@[expose] def NilesNaturalFiltration
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) : Prop :=
  ∃ V : Subgroup G, ∃ hV : V.Normal,
    letI := hV
    V = centerIn (pCore 2 G) ∧ IsElementaryAbelian 2 V ∧
      IsElementaryAbelian 2 (center G) ∧
      ((⁅(⊤ : Subgroup G),pCore 2 G⁆ ≤ V ∧
        IsElementaryAbelian 2 ((pCore 2 G).map (QuotientGroup.mk' V))) ∨
      ∃ N M : Subgroup G, ∃ hN : N.Normal, ∃ hM : M.Normal,
        letI := hN
        letI := hM
        V ≤ N ∧ N ≤ M ∧ M ≤ pCore 2 G ∧
          ⁅(⊤ : Subgroup G),N⁆ ≤ V ∧ ⁅(⊤ : Subgroup G),pCore 2 G⁆ ≤ M ∧
          IsElementaryAbelian 2 ((pCore 2 G).map (QuotientGroup.mk' M)) ∧
          IsElementaryAbelian 2 (N.map (QuotientGroup.mk' V)) ∧
          IsElementaryAbelian 2 (M.map (QuotientGroup.mk' N)) ∧
          N.relIndex M = Nat.card F ^ 2 ∧
          commutatorPreimage ⊤ M N = pCore 2 G ∧
          Nonempty (BinaryConjugationSection (⊤ : Subgroup G) M N
            (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp
              (e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 G)).comp
                (⊤ : Subgroup G).subtype)))))

/-- Niles 5.5's two natural factors at the unchanged original field degree. -/
theorem original_sl2_natural_layers
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesCenterCoordinates e ∧ NilesNaturalFiltration e := by
  refine ⟨original_sl2_natural_center e hn hF S α hfit hno,?_⟩
  obtain ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hVn,hbranch⟩ :=
    original_sl2_exact_layers e hn hF S α hfit hno
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  let φ := twistedConjugacy (S : Subgroup G) α g
  let X := intervalDiagram φ (3*v)
  let V := X v (2*v)
  let _ : V.Normal := hVn
  have hV : IsElementaryAbelian 2 V := hshort v (2*v) (by omega) (by omega)
  have hZ : IsElementaryAbelian 2 (center G) := by
    rw [hzg]
    exact hshort (v+1) (2*v-1) (by omega) (by omega)
  refine ⟨V,hVn,hzq.symm,hV,hZ,?_⟩
  rcases hbranch with hc | ⟨k,hk,hkw,hparam,heven,hex,hgap,hN,hM,hVN,hNM,hMQ,hNV,hQM,hMQZ,hd,hidx,hEq,hEn,hEm,hkernel⟩
  · exact Or.inl ⟨hc.2.1,hc.2.2⟩
  · apply Or.inr
    let N := X (3*v-k+1) (k-1)
    let M := X (3*v-k) k
    let _ : N.Normal := hN
    let _ : M.Normal := hM
    let _ : IsElementaryAbelian 2 (M.map (QuotientGroup.mk' N)) := hEm
    have hindex : ∀ a : ℕ, 1 ≤ a → a ≤ 2*v → rectangleStepIndex φ a = Nat.card F := by
      have hfirst : rectangleStepIndex φ 1 = Nat.card F := by
        let P : IntersectionPair G := ⟨S,T,φ⟩
        exact P.rectangleStepIndex_eq_index 0 hnum
      have hlast := hnum.rectangleStepIndex_double_eq_index v hv
        (by simpa only [intervalDiagram,show 3*v-(2*v-1)=v+1 by omega] using hzs)
        (by simpa only [hinter,intervalDiagram,show 3*v-2*v=v by omega] using hzq)
      change rectangleStepIndex φ (2*v) = Nat.card F at hlast
      intro a ha haw
      apply le_antisymm
      · simpa only [hfirst] using rectangleStepIndex_antitone φ ha
      · simpa only [hlast] using rectangleStepIndex_antitone φ haw
    obtain ⟨hNA,hAM,hNB,hBM,hSA,hTB,hiA,hiB⟩ :=
      intervalDiagram_gap_fixed_halves φ v k (Nat.card F) hk hkw hparam.le
        hj hzs hzt hgap hindex
    have hiS : (pCore 2 G).relIndex (S : Subgroup G) = Nat.card F := by
      rw [←hinter]
      exact hnum.index_left
    have hnatural := Representation.SL2.natural_section_of_fixed_halves e hn hF S T hgen hiS
      M N (X (3*v-k) (k-1)) (X (3*v-k+1) k) hNM hkernel hidx
      hAM hBM hSA hTB hiA hiB
    exact ⟨N,M,hN,hM,hVN,hNM,hMQ,hNV,hQM,hEq,hEn,hEm,hidx,hkernel,hnatural⟩
end Glauberman
