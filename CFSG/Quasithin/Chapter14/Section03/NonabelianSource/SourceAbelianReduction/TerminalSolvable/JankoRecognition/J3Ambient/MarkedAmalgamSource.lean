module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicNormalizerMarkedComplement
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.PlaneDerivedIntersection
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CompletionCubicGeneration

/-!
# Actual marked generating subgroups for the J₃ amalgam

The cubic-normalizer complement retains the original dihedral overlap and
its commuting inverter. Its intersection with the original plane normalizer
is exactly the original derived GL₂(4) subgroup. This same complement and
the original L₂(16):2 completion generate the whole ambient group.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The actual cubic complement preserves both shared subgroups and gives
whole-group generation with the same original sixteen-field completion. -/
theorem literal_marked_amalgam_source
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    let s := j cubic
    let f := j SingerField.fieldElement
    let N := normalizer (zpowers s : Set G)
    let D₀ := (_root_.commutator (centralizer ({s} : Set G))).map
      (inclusion (cubic_centralizer_le_normalizer s))
    ∃ (B : Subgroup G) (y : N) (K : Subgroup N),
      (∀ x, x ∈ B ↔ x ∈ overlap j ∧ x ^ 10 = 1) ∧
      Nonempty (B ≃* DihedralGroup 5) ∧ f ∈ B ∧
      (y : G) ∈ normalizer (overlap j : Set G) ∧ orderOf y = 2 ∧
      (y : G) * s * (y : G)⁻¹ = s⁻¹ ∧
      (∀ b ∈ B, Commute (y : G) b) ∧
      K = D₀ ⊔ zpowers y ∧
      (cubicNormalizerKernel s).IsComplement' K ∧
      Nonempty (K ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∧
      B ≤ K.map N.subtype ∧
      normalizer (overlap j : Set G) ⊓ K.map N.subtype = B ⊔ zpowers (y : G) ∧
      Nonempty ((normalizer (overlap j : Set G) ⊓ K.map N.subtype : Subgroup G) ≃*
        (Multiplicative (ZMod 2) × DihedralGroup 5)) ∧
      normalizer (A : Set G) ⊓ K.map N.subtype =
        (_root_.commutator C).map ((normalizer (A : Set G)).subtype.comp C.subtype) ∧
      Nonempty ((normalizer (A : Set G) ⊓ K.map N.subtype : Subgroup G) ≃*
        alternatingGroup (Fin 5)) ∧
      completion j.range (overlap j) ⊔ K.map N.subtype = ⊤ := by
  classical
  let s := j cubic
  let N := normalizer (zpowers s : Set G)
  let Z := centralizer ({s} : Set G)
  let V := cubicNormalizerKernel s
  let i : Z →* N := inclusion (cubic_centralizer_le_normalizer s)
  let D0 := _root_.commutator Z
  let Dg := D0.map Z.subtype
  let E := (_root_.commutator C).map
    ((normalizer (A : Set G)).subtype.comp C.subtype)
  obtain ⟨B,y,K,hB,eB,hfB,hyL,hy2,hyinv,hyB,hKeq,hK,eK,hBK,hpair,ePair⟩ :=
    literal_cubic_normalizer_marked_complement P hc A C l a ha j hj
  let KA := K.map N.subtype
  have hDK : Dg ≤ KA := by
    rintro x ⟨d,hd,rfl⟩
    refine ⟨i d,?_,rfl⟩
    rw [hKeq]
    exact mem_sup_left (mem_map_of_mem i hd)
  obtain ⟨hVD,_⟩ := literal_cubic_derived_factor P hc A C l a ha j hj
  have hZK : Z ⊓ KA = Dg := by
    apply le_antisymm
    · intro x hx
      let z : Z := ⟨x,hx.1⟩
      obtain ⟨⟨v,d⟩,hvd⟩ := hVD.2 z
      have heq : ((v : Z) : G) * ((d : Z) : G) = x := congrArg Subtype.val hvd
      have hdK : ((d : Z) : G) ∈ KA := hDK (mem_map_of_mem Z.subtype d.property)
      have hvK : ((v : Z) : G) ∈ KA := by
        have hh := KA.mul_mem hx.2 (KA.inv_mem hdK)
        rw [← heq,mul_inv_cancel_right] at hh
        exact hh
      obtain ⟨u,hu,heu⟩ := hvK
      have huV : u ∈ V := by
        change (u : G) ∈ zpowers s
        change (u : G) = ((v : Z) : G) at heu
        rw [heu]
        exact v.property
      have hu1 := disjoint_def.mp hK.disjoint huV hu
      have hv1 : ((v : Z) : G) = 1 := heu.symm.trans (congrArg Subtype.val hu1)
      rw [hv1,one_mul] at heq
      exact heq ▸ mem_map_of_mem Z.subtype d.property
    · exact le_inf (map_subtype_le _) hDK
  obtain ⟨hplane,ePlane⟩ := literal_plane_cubic_derived_intersection P hc A C l a hC ha j hj
  change normalizer (A : Set G) ⊓ Dg = E at hplane
  have hplaneK : normalizer (A : Set G) ⊓ KA = E := by
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ C.map (normalizer (A : Set G)).subtype := by
        rw [← PlaneTransport.field_cubic_normalizer_intersection A C l a hC ha j hj]
        exact ⟨hx.1,map_subtype_le _ hx.2⟩
      have hxZ : x ∈ Z := by
        obtain ⟨c,hc,rfl⟩ := hxC
        exact mem_centralizer_singleton_iff.mpr
          (PlaneTransport.field_cubic_centralizes_complement A C l a ha j hj ⟨c,hc⟩).symm.eq
      exact hplane ▸ ⟨hx.1,hZK ▸ (show x ∈ Z ⊓ KA from ⟨hxZ,hx.2⟩)⟩
    · intro x hx
      have hh : x ∈ normalizer (A : Set G) ⊓ Dg := hplane.symm ▸ hx
      exact ⟨hh.1,hDK hh.2⟩
  have hVK : zpowers s ⊔ KA = N := by
    have hh := congrArg (Subgroup.map N.subtype) hK.sup_eq_top
    have hVmap : V.map N.subtype = zpowers s := by
      change ((zpowers s).subgroupOf N).map N.subtype = zpowers s
      rw [subgroupOf_map_subtype,inf_eq_left.mpr (zpowers s).le_normalizer]
    rw [Subgroup.map_sup,hVmap,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hgen : completion j.range (overlap j) ⊔ KA = ⊤ := by
    apply top_unique
    rw [← literal_completion_cubic_normalizer_generate P hc A C a j hj]
    refine sup_le le_sup_left ?_
    change N ≤ completion j.range (overlap j) ⊔ KA
    rw [← hVK]
    exact sup_le ((zpowers_le.mpr (show s ∈ completion j.range (overlap j) from
      mem_sup_left ⟨cubic,rfl⟩)).trans le_sup_left) le_sup_right
  refine ⟨B,y,K,hB,eB,hfB,hyL,hy2,hyinv,hyB,hKeq,hK,eK,hBK,hpair,ePair,hplaneK,?_,hgen⟩
  obtain ⟨e⟩ := ePlane
  exact ⟨(MulEquiv.subgroupCongr hplaneK).trans e⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
