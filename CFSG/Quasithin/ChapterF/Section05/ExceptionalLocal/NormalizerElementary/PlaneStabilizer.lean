module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.Source
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPlaneAction

/-!
# The original local plane stabilizer and its quotient

Inside A₂, the elements conjugate to the graph involution whose product with
z has that same class form the marked pair {t,tz}. An element of M₁ normalizing
A₂ preserves this pair. The known T-conjugacy between its two elements and
C_M₁(t)=C_T(t) put this normalizer inside T; the wreath coordinates then give
M₁ ∩ N_G(A₂)=C_T(t). The original nine-root action recognizes the full quotient
N_G(A₂)/A₂ as S₃ × S₃, with every source premise discharged.

Source: Aschbacher–Smith F.5.4(4) and its proof, printed p.301.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (t : G) (hf : FusionFacts c i z t)
local notation "f" => Source.graphElement c i
local notation "r" => rootElement c i z

include h hf in
private theorem plane_stabilizer_eq_of_pair
    (hp : ∀ a∈A c i true, (IsConj f a ∧ IsConj f (r*a)) ↔ a=t ∨ a=t*r) :
    M c i false ⊓ normalizer (A c i true : Set G)=Tcentralizer c i t := by
  have htA : t∈A c i true := by
    apply plane_graph_core_le_A c i z h t hf
    apply le_sup_left (a := Q c i true ⊓ C c i) (b := zpowers f)
    rw [fusion_t_eq_marked_short c i z h t hf]
    exact ⟨source_short_mem_Q c i,mem_centralizer_singleton_iff.mpr (source_short_commutes_graph c i).eq⟩
  apply le_antisymm
  · intro n hnM
    let e := MulAut.conj n
    have hez : e r=r := by
      have hc : n∈centralizer ({r} : Set G) := hf.root_centralizer.symm ▸ hnM.1
      change n*r*n⁻¹=r
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc)
    have hpt := (hp t htA).mpr (Or.inl rfl)
    have heA : e t∈A c i true := (mem_normalizer_iff.mp hnM.2 t).mp htA
    have hepair : e t=t ∨ e t=t*r := by
      apply (hp (e t) heA).mp
      refine ⟨hpt.1.trans (isConj_iff.mpr ⟨n,rfl⟩),?_⟩
      have hh := hpt.2.trans (isConj_iff.mpr ⟨n,rfl⟩ : IsConj (r*t) (e (r*t)))
      simpa only [map_mul,hez] using hh
    have hnT : n∈Source.sylowImage c i := by
      rcases hepair with he | he
      · have hc : n∈centralizer ({t} : Set G) :=
          mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
        exact ((normalizer_point_short_centralizer c i z h t hf).le ⟨hnM.1,hc⟩).1
      · obtain ⟨y,hy,hye⟩ := hf.t_fuses_t_root
        have hyM := sylowImage_le_M c i false hy
        have hynt : (y⁻¹*n)*t*(y⁻¹*n)⁻¹=t := by
          change n*t*n⁻¹=t*r at he
          calc
            _ = y⁻¹*(n*t*n⁻¹)*y := by group
            _ = y⁻¹*(y*t*y⁻¹)*y := by rw [he,hye]
            _ = t := by group
        have hc : y⁻¹*n∈centralizer ({t} : Set G) :=
          mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hynt)
        have hyntT := ((normalizer_point_short_centralizer c i z h t hf).le
          ⟨(M c i false).mul_mem ((M c i false).inv_mem hyM) hnM.1,hc⟩).1
        simpa only [mul_inv_cancel_left] using (Source.sylowImage c i).mul_mem hy hyntT
    exact (normalizer_plane_A_in_T c i z h t hf).le ⟨hnT,hnM.2⟩
  · intro n hnT
    have hnorm := (normalizer_plane_A_in_T c i z h t hf).symm.le hnT
    exact ⟨sylowImage_le_M c i false hnorm.1,hnorm.2⟩

include h hf in
/-- The literal plane normalizer in the first endpoint is the marked short
centralizer inside the original Sylow subgroup. -/
theorem normalizer_local_plane_of_source :
    M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t := by
  apply plane_stabilizer_eq_of_pair c i z h t hf
  intro a ha
  rw [fusion_t_eq_marked_short c i z h t hf]
  exact source_plane_short_pair c i z h a ha

include h hf in
/-- The original plane normalizer quotient, with the local stabilizer and
root-transitivity inputs supplied by the source hypotheses. -/
theorem normalizer_plane_quotient_of_source :
    Nonempty (normalizerQuotient c i true ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  obtain ⟨S,hS⟩ := hf.sylow
  have hT : IsPGroup 2 (Source.sylowImage c i) := hS ▸ S.isPGroup'
  have hp : IsPGroup 2 (Tf c i) := hT.comap_subtype
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  exact normalizer_plane_quotient_of_transitive c i z t hf R hR
    (normalizer_root_transitive c i z h t hf true)
    (normalizer_local_plane_of_source c i z h t hf)

include h in
/-- The local plane stabilizer from the original F.5 hypotheses alone. -/
theorem source_normalizer_local_plane :
    M c i false ⊓ normalizer (A c i true : Set G) =
      Tcentralizer c i (sourceMarkedShort c i) :=
  normalizer_local_plane_of_source c i z h (sourceMarkedShort c i) (source_fusionFacts c i z h)

include h in
/-- The plane normalizer quotient from the original F.5 hypotheses alone. -/
theorem source_normalizer_plane_quotient :
    Nonempty (normalizerQuotient c i true ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  normalizer_plane_quotient_of_source c i z h (sourceMarkedShort c i) (source_fusionFacts c i z h)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
