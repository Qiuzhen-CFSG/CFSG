module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The conjugate-generation hypothesis of MS93 (2.3)

The actual marked quotient of each M-vertex stabilizer is SL3(2), with
kernel Q_alpha. A subgroup of the edge kernel escaping Q_alpha has
nontrivial normal image in that simple quotient. Its stabilizer conjugates
therefore generate the stabilizer together with Q_alpha, and hence with
the edge kernel. This establishes source (2.3)(b), without a generation
premise or a finiteness assumption on the free amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), (2.3)(b), p.857.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo
open NormalizerTransfer

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

-- The quotient transport is the same native embedding calculation as in
-- SectionThree.NormalizationTransfer.local_projection; it is private there.
private theorem local_projection (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl, ← map_map,
      ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  refine ⟨source.projection.comp e.symm.toMonoidHom,
    source.projection_surjective.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, source.projection_kernel, ← hQ]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    change e.symm (e y) ∈ pCore 2 M
    rw [MulEquiv.symm_apply_apply]
    exact hy

/-- Any edge subgroup escaping Q_alpha generates the local group by its
actual local conjugates together with the edge kernel. -/
theorem edge_conjugate_generation (source : LocalSource L R)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (J : Subgroup (FreeAmalgam R)) (hJ : J ≤ Q R b) (hnot : ¬ J ≤ Q R a) :
    conjugatesIn J (stabilizer R a) ⊔ Q R b = stabilizer R a := by
  let F := stabilizer R a
  let N := conjugatesIn J F
  have hTF : Q R b ≤ F := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hQF : Q R a ≤ F := fun _ hx => hx.1
  have hNF : N ≤ F := conjugatesIn_le J F (hJ.trans hTF)
  have hJN : J ≤ N := by
    intro x hx
    apply le_iSup (fun g : F => rightConjugate J g) (1 : F)
    exact ⟨x, hx, by simp⟩
  let : (N.subgroupOf F).Normal := normal_subgroupOf_of_le_normalizer
    (conjugatesIn_normalized J F)
  obtain ⟨π, hπ, hker⟩ := local_projection source a ha
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hn : ((N.subgroupOf F).map π).Normal :=
    (inferInstance : (N.subgroupOf F).Normal).map π hπ
  have htop : (N.subgroupOf F).map π = ⊤ := by
    rcases hn.eq_bot_or_eq_top with hh | hh
    · have hNker := (Subgroup.map_eq_bot_iff (N.subgroupOf F)).mp hh
      rw [hker] at hNker
      exact (hnot (fun x hx => hNker (show (⟨x, hNF (hJN hx)⟩ : F) ∈
        N.subgroupOf F from hJN hx))).elim
    · exact hh
  have hjoin : N.subgroupOf F ⊔ (Q R a).subgroupOf F = ⊤ := by
    have hh := congrArg (Subgroup.comap π) htop
    simpa only [comap_map_eq, hker, comap_top] using hh
  have hNQ : N ⊔ Q R a = F := by
    have hh := congrArg (Subgroup.map F.subtype) hjoin
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hNF, map_subgroupOf_eq_of_le hQF,
      ← MonoidHom.range_eq_map, range_subtype] using hh
  have hb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  exact le_antisymm (sup_le hNF hTF)
    (hNQ.symm.le.trans (sup_le_sup_left (Q_le_adjacent_h R hb hab) N))

/-- The elementwise formulation printed as source (2.3)(b). -/
theorem edge_element_conjugate_generation (source : LocalSource L R)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (x : FreeAmalgam R) (hx : x ∈ Q R b) (hnot : x ∉ Q R a) :
    conjugatesIn (zpowers x) (stabilizer R a) ⊔ Q R b = stabilizer R a := by
  exact edge_conjugate_generation source a b ha hab (zpowers x) (zpowers_le.mpr hx)
    (fun h => hnot (h (mem_zpowers x)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo
