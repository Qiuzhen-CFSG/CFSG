module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.LiteralQuotient
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.Source
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicRecognition

/-!
# Splitting on the cubic of the literal field embedding

The plane calculation supplies a split cubic normalizer. Both this cubic
and the cubic in the actual field embedding centralize involutions, so
the proved source fusion argument conjugates one to the other. Conjugation
transports the cubic kernel and its complement together. The resulting
PGL₂(9) marking is defined by the quotient projection of this same cubic.

No replacement field embedding or A₅ complement in an involution
centralizer is assumed. This aligns the Lemma 2.4 splitting with the
literal L₁₂ used in Lemma 2.5 and the original terminal application.
Source: Baumeister, A geometry for groups of J₃-type (2007), pp.495–496.
-/

open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
open LocalSixteen
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
variable {G : Type*} [Group G] [Finite G] {D : LocalSixteen.Seed G}

private theorem kernel_complement_conjugate (u v : G) (hc : IsConj u v)
    (M : Subgroup (normalizer (zpowers u : Set G)))
    (hM : (cubicNormalizerKernel u).IsComplement' M) :
    ∃ M' : Subgroup (normalizer (zpowers v : Set G)),
      (cubicNormalizerKernel v).IsComplement' M' := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let a := MulAut.conj g
  have hz : (zpowers u).map a.toMonoidHom = zpowers v := by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers hg
  have hn : (normalizer (zpowers u : Set G)).map a.toMonoidHom =
      normalizer (zpowers v : Set G) := by rw [map_equiv_normalizer_eq,hz]
  let f : normalizer (zpowers u : Set G) ≃* normalizer (zpowers v : Set G) :=
    (a.subgroupMap _).trans (MulEquiv.subgroupCongr hn)
  have hkernel (x : normalizer (zpowers u : Set G)) :
      f x ∈ cubicNormalizerKernel v ↔ x ∈ cubicNormalizerKernel u := by
    change a (x : G) ∈ zpowers v ↔ (x : G) ∈ zpowers u
    rw [← hz,mem_map_equiv]
    simp only [a.symm_apply_apply]
  have hmap : (cubicNormalizerKernel u).map f.toMonoidHom = cubicNormalizerKernel v := by
    ext x
    rw [mem_map_equiv]
    simpa only [f.apply_symm_apply] using (hkernel (f.symm x)).symm
  refine ⟨M.map f.toMonoidHom,?_⟩
  rw [← hmap]
  apply isComplement'_of_card_mul_and_disjoint
  · rw [card_map_of_injective f.injective,card_map_of_injective f.injective,
      ← Nat.card_congr f.toEquiv]
    exact hM.card_mul_card
  · apply disjoint_def.mpr
    intro x hx hy
    have hx' := mem_map_equiv.mp hx
    have hy' := mem_map_equiv.mp hy
    have hh : f.symm x = 1 := disjoint_def.mp hM.disjoint hx' hy'
    exact f.symm.injective (hh.trans f.symm.map_one.symm)

private theorem plane_split_cubic_witness
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ u v : G, orderOf u = 3 ∧ orderOf v = 2 ∧ Commute u v ∧
      ∃ M : Subgroup (normalizer (zpowers u : Set G)),
        (cubicNormalizerKernel u).IsComplement' M := by
  obtain ⟨C,s,hC,hcardC,hsc,hs,⟨e⟩⟩ :=
    plane_cubic_quotient_alternatingSix P hc A hA hAR
  obtain ⟨M,eQ,eM,hM,_⟩ := normalizer_complement_projective_of_plane_cubic
    P hc A hA hAR C hC s hsc hs e
  let u : G := ((s : normalizer (A : Set G)) : G)
  have hu : orderOf u = 3 := (orderOf_coe (s : normalizer (A : Set G))).trans
    ((orderOf_coe s).trans hs)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hcardC]; decide)
  let v : G := ((t : normalizer (A : Set G)) : G)
  have hv : orderOf v = 2 := (orderOf_coe (t : normalizer (A : Set G))).trans
    ((orderOf_coe t).trans ht)
  have huv : Commute u v := by
    exact (congrArg (fun x : C => ((x : normalizer (A : Set G)) : G))
      (mem_center_iff.mp hsc t)).symm
  exact ⟨u,v,hu,hv,huv,M,hM⟩

private theorem field_kernel_complement
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j) :
    ∃ M : Subgroup (normalizer (zpowers (j cubic) : Set G)),
      (cubicNormalizerKernel (j cubic)).IsComplement' M := by
  obtain ⟨u,v,hu,hv,huv,M,hM⟩ := plane_split_cubic_witness P hc A hA hAR
  have hs' : orderOf (j cubic) = 3 := (orderOf_injective j hj cubic).trans cubic_order
  have hsf : Commute (j cubic) (j fieldElement) :=
    (mem_centralizer_singleton_iff.mp
      (overlap_le_cubic_centralizer j (image_involution_mem j))).symm
  have hconj : IsConj u (j cubic) := cubics_conjugate_of_commuting_involutions P hc
    u (j cubic) v (j fieldElement) hu hs' hv (image_involution_order j hj) huv hsf
  obtain ⟨M',hM'⟩ := kernel_complement_conjugate u (j cubic) hconj M hM
  exact ⟨M',hM'⟩

private theorem field_projective_quotient
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (j : Model →* G) (hj : Function.Injective j) :
    Nonempty ((normalizer (zpowers (j cubic) : Set G) ⧸ cubicNormalizerKernel (j cubic)) ≃*
      GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  have hs' : orderOf (j cubic) = 3 := (orderOf_injective j hj cubic).trans cubic_order
  have he6 : Nonempty ((centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) ≃*
      alternatingGroup (Fin 6)) :=
    field_cubic_quotient (G := G) (z := D.z) D.localType hc j hj
  obtain ⟨e6⟩ := he6
  obtain ⟨e9⟩ := cubic_normalizer_quotient_pgl_nine P hc (j cubic) hs' e6
  exact ⟨e9⟩

private theorem complement_quotient_marking {H X : Type*} [Group H] [Group X]
    (K : Subgroup H) [K.Normal] (M : Subgroup H) (hM : K.IsComplement' M)
    (eQ : (H ⧸ K) ≃* X) :
    ∃ eM : M ≃* X, ∀ x : M, eM x = eQ (QuotientGroup.mk' K x.val) :=
  ⟨hM.symm.QuotientMulEquiv.symm.trans eQ,fun _ => rfl⟩

/-- The normalizer of the cubic selected by the given field embedding splits,
with its complement marking equal pointwise to the original quotient map. -/
theorem field_cubic_normalizer_complement
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j) :
    ∃ (M : Subgroup (normalizer (zpowers (j cubic) : Set G)))
      (eQ : (normalizer (zpowers (j cubic) : Set G) ⧸ cubicNormalizerKernel (j cubic)) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
      (eM : M ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F),
      (cubicNormalizerKernel (j cubic)).IsComplement' M ∧
      ∀ x : M, eM x = eQ (QuotientGroup.mk' (cubicNormalizerKernel (j cubic)) x.val) := by
  exact (field_kernel_complement P hc A hA hAR j hj).elim fun M hM =>
    (field_projective_quotient P hc j hj).elim fun eQ =>
      (complement_quotient_marking (cubicNormalizerKernel (j cubic)) M hM eQ).elim
        fun eM heM => ⟨M,eQ,eM,hM,heM⟩

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
