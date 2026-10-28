module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Neighbors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.Characteristic

/-!
# General characteristic-centralizer transfer for MS93 (4.2)(i)

The genuine neighboring span is characteristic in the edge group. Its
containment in the edge displacement times D splits the span, so source
minimality applied to its intrinsic centralizer makes the whole edge group
centralize the span. The fixed-subgroup identity gives containment in Z_beta.

This proves the group-theoretic assembly for arbitrary b > 2. The two marked
neighbor bounds in `edgeTransfer_of_neighbor_steps` are explicit remaining
premises; that conditional theorem is not the completed source theorem.
The marked-extension and edge-action arguments must discharge both premises.

Source: Meierfrankenfeld--Stellmacher (1993), (4.2)(i), printed p.882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)

include hb modules in
/-- Conditional transfer at the distinguished edge, using the original
embeddings of R, O_2(M), and L into the free amalgam. -/
theorem edge_transfer_base_of_span
    (hspan : edgeSpan R (beta R) ≤
      ⁅Z R (alpha R), Q R (beta R)⁆ ⊔ fixedCore R (alpha R)) :
    ⁅Z R (alpha R), Q R (beta R)⁆ ≤ Z R (beta R) := by
  let f := embedM R
  let W := (edgeSpan R (beta R)).comap f
  let A := (⁅Z R (alpha R), Q R (beta R)⁆).comap f
  let D := (fixedCore R (alpha R)).comap f
  have hE : ⁅Z R (alpha R), Q R (beta R)⁆ ≤ Z R (alpha R) :=
    (edge_commutator_le_natural hb modules _ _ rfl (base_adjacent R)).trans (U_le_Z _)
  have hErange : ⁅Z R (alpha R), Q R (beta R)⁆ ≤ f.range :=
    hE.trans (by simpa only [alpha, stabilizer_m_base, Mbar, f] using Z_le_stabilizer R (alpha R))
  have hDrange : fixedCore R (alpha R) ≤ f.range := by
    exact inf_le_left.trans (by
      simpa only [alpha, stabilizer_m_base, Mbar, f] using
        (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1))
  have hWQ := edgeSpan_le_kernel R hb modules (beta R) rfl
  have hWrange : edgeSpan R (beta R) ≤ f.range :=
    hWQ.trans (by rw [Q_beta]; exact map_le_range _ _)
  have hWR : W ≤ R := by
    have hh := comap_mono (f := f) hWQ
    rw [Q_beta, comap_map_eq_self_of_injective (embedM_injective R)] at hh
    exact hh
  have hchar : (W.subgroupOf R).Characteristic := by
    have heq : W.subgroupOf R = (edgeSpan R (beta R)).comap (embedS R) := by
      ext r
      change embedM R (r : M) ∈ edgeSpan R (beta R) ↔ _
      rw [show embedM R (r : M) = embedS R r from
        DFunLike.congr_fun (embedM_comp_subtype R) r]
      rfl
    rw [heq]
    exact edgeSpan_characteristic R
  have hAW : A ≤ W := comap_mono (displacement_le_edgeSpan R (base_adjacent R))
  have hWD : W ≤ A ⊔ D := by
    change (edgeSpan R (beta R)).comap f ≤ _
    rw [show A ⊔ D =
      (⁅Z R (alpha R), Q R (beta R)⁆ ⊔ fixedCore R (alpha R)).comap f from
      comap_sup_eq_of_le_range f hErange hDrange]
    exact comap_mono hspan
  have hQA : pCore 2 M ≤ centralizer (A : Set M) := by
    intro q hq a ha
    apply embedM_injective R
    have hq' : embedM R q ∈ Q R (alpha R) := by
      rw [Q_alpha R source.two_group source.core_le]
      exact mem_map_of_mem _ hq
    have hh := (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes (alpha R) rfl)) (hE ha) _ hq'
    simpa only [map_mul] using hh.symm
  have hDQ : D ≤ pCore 2 M := by
    have hh := comap_mono (f := f)
      (show fixedCore R (alpha R) ≤ Q R (alpha R) from inf_le_left)
    rw [Q_alpha R source.two_group source.core_le,
      comap_map_eq_self_of_injective (embedM_injective R)] at hh
    exact hh
  have hLD : L ≤ centralizer (D : Set M) := by
    intro l hl d hd
    apply embedM_injective R
    have hl' : embedM R l ∈ Ltilde R (alpha R) := by
      rw [Ltilde_alpha, source.residual]
      exact mem_map_of_mem _ hl
    have hh := hd.2 _ hl'
    simpa only [map_mul] using hh.symm
  have hc := DistanceFour.Early.Containment.Transfer.centralizes_of_minimal_and_split
    source.minimal source.core_le
    hWR hchar hAW hWD hQA hDQ hLD
  have hCW : Q R (beta R) ≤ centralizer (edgeSpan R (beta R) : Set (FreeAmalgam R)) := by
    have hh := (map_mono (f := f) hc).trans
      (map_centralizer_le_centralizer_image (W : Set M) f)
    change R.map f ≤ centralizer (W.map f : Set (FreeAmalgam R)) at hh
    change R.map f ≤ centralizer (((edgeSpan R (beta R)).comap f).map f : Set _) at hh
    rw [map_comap_eq_self hWrange] at hh
    rw [Q_beta]
    exact hh
  rw [edge_Z_eq_fixed hb modules (alpha R) (beta R) rfl (base_adjacent R)]
  exact le_inf hE ((displacement_le_edgeSpan R (base_adjacent R)).trans
    (le_centralizer_iff.mp hCW))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
variable {M : Type*} [Group M] (R : Subgroup M)

private theorem map_centralizer_equiv {G : Type*} [Group G]
    (E : Subgroup G) (f : G ≃* G) :
    (centralizer (E : Set G)).map f.toMonoidHom =
      centralizer (E.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

/-- Conjugation covariance for the source fixed core D_alpha. -/
theorem fixedCore_act (g : FreeAmalgam R) (a : Vertex R) :
    fixedCore R (act R g a) = (fixedCore R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [fixedCore, Q_act, Ltilde_act, fixedCore,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, map_centralizer_equiv]

variable [Finite M] {L : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R} (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)

include hb modules in
/-- The characteristic-centralizer transfer at every edge, conditional on
the source span containment. The marked-module argument supplying `hspan`
from the neighboring B_alpha containments remains a separate obligation. -/
theorem edge_transfer_of_span (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b)
    (hspan : edgeSpan R b ≤ ⁅Z R a, Q R b⁆ ⊔ fixedCore R a) :
    ⁅Z R a, Q R b⁆ ≤ Z R b := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a b).mp hab
  · have hm : act R g (alpha R) = mVertex R g := by simp only [alpha, act_mVertex, one_mul]
    have hh : act R g (beta R) = hVertex R g := by simp only [beta, act_hVertex, one_mul]
    rw [← hm, ← hh] at hspan ⊢
    simp only [edgeSpan_act, fixedCore_act, Z_act, Q_act, ← map_commutator,
      ← Subgroup.map_sup] at hspan ⊢
    exact map_mono (edge_transfer_base_of_span hb modules
      ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hspan))
  · cases ha

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
