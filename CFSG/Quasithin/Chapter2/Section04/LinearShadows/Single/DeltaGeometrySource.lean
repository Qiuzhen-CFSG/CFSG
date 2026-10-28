module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ThompsonNormalSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.GeneratedCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterClosureSource
/-!
# Generated centralizers of the two-coordinate orbit

The actual Δ-centrality theorem puts C_G(u) inside M, and the preceding
normality theorem makes R normal in M. Sylow transport and the whole-Z
closure theorem then put every generated two-subgroup of C_G(u) inside R.
In particular this applies to any conjugate of Z(R), since its two source
center factors are whole conjugates of Z. The final theorem is the exact
centralizer-containment application used in the proof of 2.4.21.

Source: Aschbacher–Smith, 2.4.20(6), 2.4.21, printed pp.535–536.
All hypotheses beyond the original single-block setup are discharged.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Original 2.4.20(6), with centralizer containment and R-normality discharged. -/
theorem source_distinguished_delta_generated_le
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (u : G) (hu : u ∈ distinguishedDelta d x)
    (X : Subgroup G) (hX : IsPGroup 2 X) (hXC : X ≤ centralizer ({u} : Set G))
    (hgen : conjugateSubgroupClosure (distinguishedZ d) X = X) :
    X ≤ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  exact source_distinguished_generated_two_subgroup_le d hG T hST hsingle hL hM hTM hunique
    (source_noncenterless_thompson_normal d hG T hST hsingle hL hM hTM hunique hz)
    X hX (hXC.trans (source_distinguished_delta_central d hG T hST hsingle hL hM hTM hunique hz
      x hxT hxS u hu).2.2.1) hgen

/-- The actual 2.4.21 consumer: a conjugate of Z(R) centralizing Δ lies in R. -/
theorem source_distinguished_delta_conjugate_center_le
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (u : G) (hu : u ∈ distinguishedDelta d x) (g : G)
    (hC : (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)).map
        (MulAut.conj g).toMonoidHom ≤ centralizer ({u} : Set G)) :
    (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)).map
        (MulAut.conj g).toMonoidHom ≤
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  have hRT : R ≤ (T : Subgroup G) := (sSup_le fun _ h => h.1).trans hST.le
  exact source_distinguished_delta_generated_le d hG T hST hsingle hL hM hTM hunique hz
    x hxT hxS u hu _ ((T.isPGroup'.to_le (inf_le_left.trans hRT)).map (MulAut.conj g).toMonoidHom) hC
    (source_distinguished_conjugate_center_closure d hG T hST hsingle hL hM hTM hunique hz g)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
