module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerResidual
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12.Aut
/-!
# The marked inner Sylow lies in the actual outer source residual

Restriction of the literal degree-24 embedding to the inner parabolics
commutes with both overlap inclusions. The inner quaternion core lies in
the first local residual, and the marked moving element lies in the second.
Their established generators therefore put the whole embedded inner Sylow
of order 64 into the original ambient two-residual. The embedding stays
injective and its image stays in the original common Sylow.

Source: Aschbacher–Smith, F.6.18(13), printed p.310; F.6.6 and 14.2.21.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
variable {G : Type*} [Group G] {G₁ G₂ : Subgroup G}
theorem outer_marked_inner_sylow_embedding
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    ∃ f : sylowCandidate →* G, Function.Injective f ∧
      f.range ≤ G₁ ⊓ G₂ ∧ f.range ≤ pResidual 2 G := by
  obtain ⟨j⟩ := hM
  let e := ((j.trans GreenBook.AutMathieuTwelve.ambientIso.symm).trans
    GreenBook.AutMathieuTwelve.concreteIso).symm
  let embS : sylowCandidate →* M12ExceptionalExtension.overlap :=
    (M12ExceptionalExtension.innerModel.embedding.comp sylowCandidate.subtype).codRestrict
      M12ExceptionalExtension.overlap (fun s => by
        change (s : M12) ∈ M12ExceptionalExtension.overlap.comap
          M12ExceptionalExtension.innerModel.embedding
        rw [M12ExceptionalExtension.SecondCoordinates.comap_overlap]
        exact s.property)
  let emb₂ : secondParabolic →* M12ExceptionalExtension.secondParabolic :=
    (M12ExceptionalExtension.innerModel.embedding.comp secondParabolic.subtype).codRestrict
      M12ExceptionalExtension.secondParabolic (fun s => by
        change (s : M12) ∈ M12ExceptionalExtension.secondParabolic.comap
          M12ExceptionalExtension.innerModel.embedding
        rw [M12ExceptionalExtension.SecondCoordinates.comap_secondParabolic]
        exact s.property)
  let f₁ : firstParabolic →* G := G₁.subtype.comp (e.left.toMonoidHom.comp
    (M12ExceptionalExtension.FirstParabolic.innerFirstEmbedding M12ExceptionalExtension.innerModel))
  let f₂ : secondParabolic →* G := G₂.subtype.comp (e.right.toMonoidHom.comp emb₂)
  let fS : sylowCandidate →* G := (G₁ ⊓ G₂).subtype.comp (e.middle.toMonoidHom.comp embS)
  have h₁ (s : sylowCandidate) :
      f₁ (Subgroup.inclusion inf_le_left s) = fS s :=
    congrArg Subtype.val (e.left_commutes (embS s))
  have h₂ (s : sylowCandidate) :
      f₂ (Subgroup.inclusion inf_le_right s) = fS s :=
    congrArg Subtype.val (e.right_commutes (embS s))
  have hcore (s : sylowCandidate) (hs : (s : M12) ∈ core) : fS s ∈ pResidual 2 G := by
    obtain ⟨a, ha, has⟩ := CoverOrbits.core_le_coverResidual hs
    have he : a = Subgroup.inclusion inf_le_left s := Subtype.ext has
    rw [he] at ha
    rw [← h₁]
    exact map_pResidual_le 2 f₁ ⟨_, ha, rfl⟩
  have hfirst : fS (SylowAutomorphismGroup.generator 0) ∈ pResidual 2 G :=
    hcore _ ((mem_core _).mpr ⟨.a 1,.a 0,by decide +kernel⟩)
  have hsecond : fS (SylowAutomorphismGroup.generator 1) ∈ pResidual 2 G :=
    hcore _ ((mem_core _).mpr ⟨.a 0,.a 1,by decide +kernel⟩)
  let c : secondParabolic := ⟨movingActor, movingActor_mem⟩
  have hc : f₂ c ∈ pResidual 2 G := map_pResidual_le 2 f₂
    ⟨c,movingActor_residual,rfl⟩
  have hthird : fS (SylowAutomorphismGroup.generator 2) ∈ pResidual 2 G := by
    rw [← h₂]
    have he : Subgroup.inclusion inf_le_right (SylowAutomorphismGroup.generator 2) =
        c * Subgroup.inclusion inf_le_right (SylowAutomorphismGroup.generator 0) * c := rfl
    rw [he, map_mul, map_mul, h₂]
    exact (pResidual 2 G).mul_mem ((pResidual 2 G).mul_mem hc hfirst) hc
  have hgenerators (i : Fin 3) : fS (SylowAutomorphismGroup.generator i) ∈ pResidual 2 G := by
    fin_cases i
    · exact hfirst
    · exact hsecond
    · exact hthird
  have hword (w : List (Fin 3)) : fS (SylowAutomorphismGroup.evaluate w) ∈ pResidual 2 G := by
    induction w with
    | nil => simpa only [SylowAutomorphismGroup.evaluate, map_one] using (pResidual 2 G).one_mem
    | cons i w ih =>
      rw [SylowAutomorphismGroup.evaluate, map_mul]
      exact (pResidual 2 G).mul_mem (hgenerators i) ih
  refine ⟨fS, ?_, ?_, ?_⟩
  · intro s t h
    apply Subtype.ext
    apply M12ExceptionalExtension.innerModel.embedding_injective
    have hs : embS s = embS t := e.middle.injective (Subtype.ext h)
    exact congrArg (fun x : M12ExceptionalExtension.overlap => (x : M12ExceptionalExtension.Carrier)) hs
  · rintro x ⟨s,rfl⟩
    exact (e.middle (embS s)).property
  · rintro x ⟨s,rfl⟩
    obtain ⟨i,hi⟩ := SylowAutomorphismGroup.element_surjective s
    have hh := hword (SylowAutomorphismGroup.words i)
    change fS (SylowAutomorphismGroup.element i) ∈ pResidual 2 G at hh
    rwa [hi] at hh
end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
