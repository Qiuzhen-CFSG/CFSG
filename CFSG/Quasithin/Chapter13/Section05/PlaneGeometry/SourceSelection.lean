module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.SourceBlock
public import Theory.GroupTheory.SylowSubgroupCentralizerAlignment
/-!
# A fully centralized nondegenerate plane in the original source

Starting from an actual nondegenerate four-subgroup W≤V, its local
centralizer lies in M_V by original L-transitivity. Sylow conjugacy inside
M_V then selects a conjugate of W for which C_T(W) is maximal among the
two-subgroups of C_M(W). The same original module and invariant form show
that this conjugate remains a nondegenerate four-subgroup of V.

Source: Aschbacher--Smith 13.5.6, printed p.917. This makes the necessary
Sylow choice explicit before the ambient normalizer-escape argument.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_fully_centralized_plane (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,form x y=0) :
    ∃g:QuadraticSource.localModuleNormalizer (M:=M) (V:=V),
      W.map (MulAut.conj g.val).toMonoidHom≤V ∧
      Nat.card (W.map (MulAut.conj g.val).toMonoidHom)=4 ∧
      (¬∀x∈image d (W.map (MulAut.conj g.val).toMonoidHom),
        ∀y∈image d (W.map (MulAut.conj g.val).toMonoidHom),form x y=0) ∧
      ∀U:Subgroup G,IsPGroup 2 U→
        planeCentralizer (T:=T) (W.map (MulAut.conj g.val).toMonoidHom)≤U→
        U≤M⊓centralizer (W.map (MulAut.conj g.val).toMonoidHom:Set G)→
        U=planeCentralizer (T:=T) (W.map (MulAut.conj g.val).toMonoidHom) := by
  have hW:W≠⊥ := by
    intro hz
    have hh:Nat.card W=1:=by rw [hz];exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
    omega
  have hTN:(T:Subgroup G)≤QuadraticSource.localModuleNormalizer (M:=M) (V:=V):=by
    apply le_inf
    · rw [d.local_normalizer];exact d.normalizes_L
    · exact le_sup_right.trans d.normalizes_V
  have hC:M⊓centralizer (W:Set G)≤QuadraticSource.localModuleNormalizer (M:=M) (V:=V):=by
    apply le_inf inf_le_left
    exact (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)).trans
      (local_plane_normalizer_le_moduleNormalizer d W hWV hW)
  obtain ⟨g,hg⟩:=Subgroup.exists_local_centralizer_alignment T M
    (QuadraticSource.localModuleNormalizer (M:=M) (V:=V)) W hTN inf_le_left hC
  refine ⟨g,?_,?_,?_,hg⟩
  · rintro _ ⟨w,hw,rfl⟩
    exact mem_normalizer_iff.mp g.property.2 w |>.mp (hWV hw)
  · rw [card_map_of_injective (MulAut.conj g.val).injective,hcard]
  · rw [QuadraticSource.image_conjugate_by_local d W hWV g]
    intro he
    apply hn
    intro x hx y hy
    have hh:=he (naturalRepresentation (Fin 6) (QuadraticSource.permutation d g) x)
      ⟨x,hx,rfl⟩ (naturalRepresentation (Fin 6) (QuadraticSource.permutation d g) y) ⟨y,hy,rfl⟩
    rwa [form_invariant] at hh
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
