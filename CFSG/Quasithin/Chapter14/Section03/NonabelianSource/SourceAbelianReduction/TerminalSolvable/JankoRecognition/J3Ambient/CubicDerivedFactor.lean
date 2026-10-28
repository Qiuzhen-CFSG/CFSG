module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicNonfusion
public import Theory.SpecificGroups.AlternatingSix.CentralThreeNonfusionSplit

/-!
# The canonical A₆ factor in the original cubic centralizer

Actual plane nonfusion splits the full central cubic kernel over the derived
subgroup itself. Thus the A₆ factor is canonical in the full original cubic
centralizer, rather than an arbitrarily chosen quotient section. This is the
marked factor needed to study the original Sylow three-subgroups.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The derived subgroup of the actual cubic centralizer is an A₆ complement
to its full original cubic kernel. -/
theorem literal_cubic_derived_factor
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    (cubicKernel (j cubic)).IsComplement' (_root_.commutator (centralizer ({j cubic} : Set G))) ∧
      Nonempty ((_root_.commutator (centralizer ({j cubic} : Set G))) ≃*
        alternatingGroup (Fin 6)) := by
  let s := j cubic
  let Z := centralizer ({s} : Set G)
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  obtain ⟨⟨eA⟩,_⟩ := literal_field_cubic_projective P hc A C a j hj
  let q : Z →* alternatingGroup (Fin 6) := eA.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel s))
  have hker : q.ker = cubicKernel s := by
    rw [MonoidHom.ker_comp_of_injective _ _ eA.injective,QuotientGroup.ker_mk']
  obtain ⟨σ,hσ,_hder,hσs,hσout,hnf⟩ := literal_cubic_nonfusion P hc A C l a ha j hj
  let x : Z := ⟨((σ : normalizer (A : Set G)) : G),mem_centralizer_singleton_iff.mpr hσs.eq.symm⟩
  let z : Z := ⟨s,cubic_le_centralizer s (mem_zpowers s)⟩
  have hx : orderOf x = 3 := (orderOf_coe _).symm.trans
    ((orderOf_coe (σ : normalizer (A : Set G))).trans ((orderOf_coe σ).trans hσ))
  have hxq : q x ≠ 1 := by
    intro hh
    have hxk : x ∈ q.ker := hh
    rw [hker] at hxk
    exact hσout hxk
  have hnon : ¬ IsConj x (z*x) := by
    intro hh
    exact hnf (Z.subtype.map_isConj hh)
  have hd := AlternatingSix.CentralThreeNonfusionSplit.kernel_complement_of_nonfusion q
    (eA.surjective.comp (QuotientGroup.mk'_surjective _))
    (hker ▸ cubicKernel_central s) (hker.symm ▸ cubicKernel_card s hs)
    x hx hxq z (hker.symm ▸ mem_zpowers s) hnon
  rw [hker] at hd
  exact ⟨hd,⟨hd.symm.QuotientMulEquiv.symm.trans eA⟩⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
