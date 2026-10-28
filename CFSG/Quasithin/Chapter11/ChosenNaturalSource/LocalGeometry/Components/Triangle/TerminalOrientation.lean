module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.G2Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.OmegaCentralization
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LocalGLSp4
public import Theory.Quasithin.CoprimeRank

/-!
# The G₂ Cartan identity at the reselected triangle vertex

The actual Borel characters split the original G₂ Cartan into its two
residual intersections. The canonical PSL₃(4) intersection calculation
therefore puts this same Cartan in I = K₀ ∨ L₂. A nontrivial common normal
two-subgroup gives three-rank two for I and its full two-core quotient.

For a reselected natural G₂ vertex, nonsolvable uniqueness and the earlier
7.0.1/3.2.5 omega-centralization argument construct the point and plane
residuals K₀ and L₂. The original Cartan transfers to this vertex. Applying
B.4.6(14) to both marked natural actions identifies, as literal ambient
subgroups, C_X(K₀/O₂(K₀)) = X ∩ L₂ = C_X(L₁/O₂(L₁)).

This supplies the G₂/G₂ centralization side of the terminal contradiction.
The incompatible action of this same cubic in the original PGL₃(4)
quotient, the Sp₄/Sp₄ argument, initial G₂ reselection and the complete
FieldFourTriangle consumer remain to be assembled. No triangle orientation
or centralization by this cubic is assumed here.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764; B.4.6(14).
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The quotient model selects the G₂ coordinates before applying the actual
Cartan-action calculation; orders are used only to exclude the other models. -/
theorem point_kernel_eq_plane_of_g2_model (hd : S.field.degree = 2)
    (hm : ClassificationModels.IsG2At (L ⧸ pCore 2 L) 4)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X) :
    X ⊓ Closure.coreQuotientCentralizer (f.Li 0) = X ⊓ f.Li 1 := by
  have hc : Nat.card (L ⧸ pCore 2 L) = 251596800 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
    norm_num
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  cases c with
  | g2 m => exact g2_point_kernel_eq_plane S m hd f hX
  | sp4 m =>
    rw [Nat.card_congr m.groupEquiv.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hc
    norm_num at hc
  | sl3 m =>
    rw [Nat.card_congr m.groupEquiv.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hc
    norm_num at hc

variable (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (.g2 m))

/-- The original G₂ Cartan lies in the literal third vertex, by the actual
PSL₃/PGL₃ intersection identities and the two residual characters. -/
theorem g2_triangle_cartan_le_join
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hd : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    X ≤ K₀ ⊔ f.Li 1 := by
  obtain ⟨_,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm₁ hd
    hX hK hLK hK₀ hK₀K hk hp
  rw [←(g2_cartan_split S m f hX).1]
  exact sup_le_sup ((h₁.symm.trans h₀).le.trans inf_le_right) inf_le_right

/-- The canonical other residual from the source construction retains the
same Cartan and the same cubic X₁. Its order is computed only after its
literal equality with X ∩ L₂ has been proved from the action. -/
theorem g2_canonical_triangle_cubic
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hd : S.field.degree = 2)
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ f.Li 0 → J = K₀) ∧
      (T : Subgroup G) ≤ normalizer (K₀ : Set G) ∧ K₀ ∈ Chapter1.He G ∧
      f.Li 0 ⊔ K₀ = K ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 ∧
      X ≤ K₀ ⊔ f.Li 1 ∧
      Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3 ∧
      X ⊓ Closure.coreQuotientCentralizer (f.Li 0) = X ⊓ f.Li 1 := by
  obtain ⟨K₀,h₀,h₀K,hne,hne₁,hunique,hn,hHe,hgen,hm₀⟩ :=
    first_triangle_other_residual D S f hm₁ hK hLK hk
  have hlt : K₀ < K := lt_of_le_of_ne h₀K hne
  have he := g2_point_kernel_eq_plane S m hd f hX
  refine ⟨K₀,h₀,h₀K,hne,hne₁,hunique,hn,hHe,hgen,hm₀,
    g2_triangle_cartan_le_join D S m f hu hm₁ hd hX hK hLK h₀ hlt hk hp,?_,he⟩
  rw [he]
  obtain ⟨hc,h₁,_⟩ := first_triangle_cartan_intersections D S f hu hm₁ hd
    hX hK hLK h₀ hlt hk hp
  have hc₁ : Nat.card (X ⊓ f.Li 0 : Subgroup G) = 3 := h₁ ▸ hc
  obtain ⟨hsplit,hdis⟩ := g2_cartan_split S m f hX
  let e := (Coordinates.g2 m).cartanTorusEquiv hX
  let : CommGroup X := MonoidHom.commGroupOfInjective e.toMonoidHom e.injective
  have hcomm : X ⊓ f.Li 1 ≤ centralizer (X ⊓ f.Li 0 : Set G) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy.1⟩ : X) (⟨x,hx.1⟩ : X))
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1)
    (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hdis
  rw [hsplit,(Coordinates.g2 m).cartan_card hX,hd,hc₁] at hh
  omega

/-- The common normal subgroup bounds the three-rank of the actual G₂
third vertex; its embedded original Cartan attains that bound. -/
theorem g2_triangle_join_three_rank
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hd : S.field.degree = 2)
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    primeRank 3 (K₀ ⊔ f.Li 1 : Subgroup G) = 2 ∧
      primeRank 3 ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) = 2 := by
  have hXI := g2_triangle_cartan_le_join D S m f hu hm₁ hd hX hK hLK hK₀ hK₀K hk hp
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨Q,hQ,T.isPGroup'.to_le hQT,rfl⟩
  have hn : K₀ ⊔ f.Li 1 ≤ normalizer (Q : Set G) := sup_le hKQ hLQ
  have hupp := (_root_.primeRank_le_of_injective 3 (inclusion hn)
    (inclusion_injective hn)).trans (hN.stronglyQuasithin 3 Nat.prime_three (by decide))
  have hlo := _root_.primeRank_le_of_injective 3 (inclusion hXI) (inclusion_injective hXI)
  rw [(Coordinates.g2 m).cartan_primeRank hX Nat.prime_three (by simp [hd])] at hlo
  have he := le_antisymm hupp hlo
  exact ⟨he,(primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans he⟩

/-- Both original residuals are proper in the third vertex, because the
same order-nine Cartan escapes each of them. -/
theorem g2_triangle_proper_residuals
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    K₀ < K₀ ⊔ f.Li 1 ∧ f.Li 1 < K₀ ⊔ f.Li 1 ∧
      ¬ X ≤ K₀ ∧ ¬ X ≤ f.Li 1 := by
  obtain ⟨hc,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hXI := g2_triangle_cartan_le_join D S m f hu hm hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hn₀ : ¬ X ≤ K₀ := by
    intro h
    have he : X ⊓ K = X := h₀.trans (inf_eq_left.mpr h)
    rw [he,(Coordinates.g2 m).cartan_card hX,hfour] at hc
    norm_num at hc
  have hn₂ : ¬ X ≤ f.Li 1 := by
    intro h
    have hd := (g2_cartan_split S m f hX).2
    rw [inf_eq_left.mpr h] at hd
    have he : X ⊓ f.Li 0 = ⊥ := disjoint_self.mp
      (Disjoint.mono_right (inf_le_left : X ⊓ f.Li 0 ≤ X) hd)
    rw [h₁,he,card_bot] at hc
    contradiction
  exact ⟨lt_of_le_of_ne le_sup_left (fun he => hn₀ (he.symm ▸ hXI)),
    lt_of_le_of_ne le_sup_right (fun he => hn₂ (he.symm ▸ hXI)),hn₀,hn₂⟩

/-- The original G₂ Cartan gives both literal GL₂(4) local quotients,
with each smaller two-core equal to the two-core of its Cartan join. -/
theorem g2_triangle_local_gl_markings
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    X ≤ normalizer (K₀ : Set G) ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 ∧
      (K₀ ⊔ X : Subgroup G).pCoreIn 2 = K₀.pCoreIn 2 ∧
      IsGLTwoFour ((K₀ ⊔ X : Subgroup G) ⧸ pCore 2 (K₀ ⊔ X : Subgroup G)) ∧
      (f.Li 1 ⊔ X : Subgroup G).pCoreIn 2 = (f.Li 1).pCoreIn 2 ∧
      IsGLTwoFour ((f.Li 1 ⊔ X : Subgroup G) ⧸ pCore 2 (f.Li 1 ⊔ X : Subgroup G)) := by
  have hXN (i : Fin 2) : X ≤ normalizer (f.Li i : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi i.castSucc : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX i.castSucc)
    exact (hx.trans (L ⊓ normalizer (f.Vi i.castSucc : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hXP : X ≤ normalizer (((T : Subgroup G) ⊓ f.Li 0 : Subgroup G) : Set G) := by
    have he : (T : Subgroup G) ⊓ f.Li 0 = ((T : Subgroup G) ⊓ L) ⊓ f.Li 0 := by
      exact le_antisymm
        (le_inf (le_inf inf_le_left (inf_le_right.trans ((localResidual_le _).trans inf_le_left))) inf_le_right)
        (inf_le_inf inf_le_left le_rfl)
    rw [he]
    exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) (hXN 0)).trans
      inf_normalizer_le_normalizer_inf
  have hNK : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  obtain ⟨hn₀,hm₀⟩ := other_local_marking_of_normalizes_intersection T ht
    ((f.invariant 0).trans hNK) (flag_mem_local_of_model D S f 0 hm₁).1 hLK hK₀.1 hK₀K
    ((f.cartan_normalizes hu hX 0).trans hNK) (hXN 0) hXP hk
  obtain ⟨hc,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hcardX : Nat.card X = 9 := by
    rw [(Coordinates.g2 m).cartan_card hX,hfour]
    norm_num
  have hcard₀ : Nat.card (X ⊓ K₀ : Subgroup G) = 3 := h₀ ▸ hc
  have hcard₁ : Nat.card (X ⊓ f.Li 0 : Subgroup G) = 3 := h₁ ▸ hc
  have hcard₂ : Nat.card (X ⊓ f.Li 1 : Subgroup G) = 3 := by
    obtain ⟨hgen,hdis⟩ := g2_cartan_split S m f hX
    let e := (Coordinates.g2 m).cartanTorusEquiv hX
    let : CommGroup X := MonoidHom.commGroupOfInjective e.toMonoidHom e.injective
    have hcomm : X ⊓ f.Li 1 ≤ centralizer (X ⊓ f.Li 0 : Set G) := by
      intro x hx y hy
      exact congrArg Subtype.val (mul_comm (⟨y,hy.1⟩ : X) (⟨x,hx.1⟩ : X))
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1)
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hdis
    rw [hgen,hcardX,hcard₁] at hh
    omega
  obtain ⟨hc₀,hg₀⟩ := residual_cartan_gl_two_four K₀ X hn₀ hm₀ hcardX hcard₀
  obtain ⟨hc₂,hg₂⟩ := residual_cartan_gl_two_four (f.Li 1) X (hXN 1)
    (by simpa [hfour] using hm₂) hcardX hcard₂
  exact ⟨hn₀,hm₀,hc₀,(isGLTwoFour_iff _).mpr hg₀,hc₂,(isGLTwoFour_iff _).mpr hg₂⟩

/-- The actual common-normal G₂ join has both marked local quotients,
relative normality, Cartan containment and three-rank two. The nontrivial Q
and the preceding second Cartan action facts remain explicit. -/
theorem g2_triangle_marked_locals_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    Source.NormalComponentIn (I ⊔ (T : Subgroup G)) I ∧
      I ∈ Chapter1.L G T ∧ I ∈ Chapter1.He G ∧ X ≤ I ∧
      primeRank 3 I = 2 ∧ primeRank 3 (I ⧸ pCore 2 I) = 2 ∧
      ∀ B : Subgroup G, B = K₀ ∨ B = f.Li 1 →
        B < I ∧ B ⊔ X ≤ I ∧ X ≤ normalizer (B : Set G) ∧
        ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 ∧
        (B ⊔ X : Subgroup G).pCoreIn 2 = B.pCoreIn 2 ∧
        IsGLTwoFour ((B ⊔ X : Subgroup G) ⧸ pCore 2 (B ⊔ X : Subgroup G)) := by
  intro I
  obtain ⟨hI,hIL,hIH,_⟩ := triangle_join_component_of_common_normal_projective
    D S f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hXI := g2_triangle_cartan_le_join D S m f hu hm₁ hfour hX hK hLK hK₀ hK₀K hk hp
  obtain ⟨hr,hrq⟩ := g2_triangle_join_three_rank D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp hQ hQT hKQ hLQ
  obtain ⟨hn₀,hm₀,hc₀,hg₀,hc₂,hg₂⟩ := g2_triangle_local_gl_markings
    D S m f hu hm₁ hm₂ hfour hX hK hLK hK₀ hK₀K hk hp
  obtain ⟨hlt₀,hlt₂,_,_⟩ := g2_triangle_proper_residuals
    D S m f hu hm₁ hfour hX hK hLK hK₀ hK₀K hk hp
  refine ⟨hI,hIL,hIH,hXI,hr,hrq,?_⟩
  intro B hB
  rcases hB with rfl | rfl
  · exact ⟨hlt₀,sup_le le_sup_left hXI,hn₀,hm₀,hc₀,hg₀⟩
  · have hn₂ : X ≤ normalizer (f.Li 1 : Set G) := by
      have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
        le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
      exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
    exact ⟨hlt₂,sup_le le_sup_right hXI,hn₂,by simpa [hfour] using hm₂,hc₂,hg₂⟩


/-- At the literal reselected G₂ vertex the original cubic X₁ centralizes
K₀/O₂(K₀). Both residual identifications and the whole-K point centralization
are constructed by the earlier-source geometry in this application. -/
theorem g2_reselected_point_kernel_of_source701325
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hd : S.field.degree = 2)
    {K K₀ X U : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives)
    (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U) (S_I : D_I.NonbinaryNaturalInput)
    (hdI : S_I.field.degree = 2)
    (hmI : ClassificationModels.IsG2At
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 4) :
    IsCartan T (K₀ ⊔ f.Li 1) X ∧
      X ⊓ Closure.coreQuotientCentralizer K₀ = X ⊓ f.Li 1 ∧
      X ⊓ Closure.coreQuotientCentralizer K₀ =
        X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ∧
      ∃ f_I : InvariantFlag (coordinates D_I S_I), f_I.IsInnerUnique ∧
        K ≤ centralizer (f_I.Vi 0 : Set G) ∧
        f_I.Li 0 = K₀ ∧ f_I.Li 1 = f.Li 1 ∧ f_I.Ri 1 = f.Ri 1 ∧
        Source.NormalComponentIn (normalizer (f_I.Vi 0 : Set G)) K ∧
        f_I.Li 0 < K ∧ K ∈ Chapter1.He G ∧
        ∀ J : Subgroup G, Source.ComponentIn (normalizer (f_I.Vi 0 : Set G)) J →
          f_I.Li 0 ≤ J → J = K := by
  have hKZ := first_projective_component_centralizes_omega_of_source701325 D S f hK hk hpre
  have hgen : f.Li 0 ⊔ f.Li 1 = L := by
    have he (i : Fin 2) : f.Li i = (G2.flag S m).Li i := by
      change localResidual L ((Coordinates.g2 m).preimage (f.space i.castSucc)) = _
      rw [G2.flag_inner_unique S m i.castSucc (f.space i.castSucc)
        (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))]
      rfl
    rw [he 0,he 1]
    exact G2.ResidualIncidence.flag_Li_sup S m
  obtain ⟨hproper₀,hproper₂,_,_⟩ := g2_triangle_proper_residuals D S m f hu hm₁ hd
    hX hK hLK hK₀ hK₀K hk hp
  obtain ⟨hf,f_I,hinner,_,hfirst,hsecond,hradical⟩ :=
    reselected_paired_flag_of_component_centralizes_omega D S f hm₁ hgen hK.1 hLK
      hK₀ hK₀K.le hproper₀ hproper₂ hKZ D_I S_I hdI (.inr hmI)
  have hXI := g2_triangle_cartan_le_join D S m f hu hm₁ hd hX hK hLK hK₀ hK₀K hk hp
  have hcartan := ShadowReduction.ComponentGeometry.Triangle.Reselection.cartan_transfer
    D S hd hX D_I S_I hdI hXI
  have hXK : X ≤ normalizer (K : Set G) :=
    (f.cartan_normalizes hu hX 0).trans
      ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hpoint := ShadowReduction.ComponentGeometry.Triangle.Reselection.component_centralizes_point_of_cartan
    D_I S_I f_I hf (simple_four_fixed_line D_I S_I hdI (.inr hmI) hf f_I)
      K X hcartan hXK hKZ
  have he := point_kernel_eq_plane_of_g2_model D_I S_I hdI hmI f_I hcartan
  rw [hfirst,hsecond] at he
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hlocalK : K ∈ Chapter1.L G T := by
    refine ⟨hK.1.2.subgroupOf_of_le le_sup_left (sup_le hK.1.1 (f.invariant 0)),
      ⟨T.subtype le_sup_right,?_⟩,?_⟩
    · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    · intro he
      apply f.V_ne_bot 0
      apply bot_unique
      have hUT : f.Vi 0 ≤ (T : Subgroup G) :=
        (D.centralQuotientPreimage_le _).trans D.le_sylow
      have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT)
        (hUT.trans (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right))
        (sup_le hK.1.1 (f.invariant 0))
      exact he ▸ hcore
  have hfirstK : f_I.Li 0 < K := by rw [hfirst]; exact hK₀K
  obtain ⟨hrelative,hHe,hunique⟩ := projective_four_relative_component_of_point_centralization
    D_I S_I f_I hdI hf (simple_four_fixed_line D_I S_I hdI (.inr hmI) hf f_I)
    hcartan hlocalK hTK hk hfirstK.le hpoint
  exact ⟨hcartan,he,he.trans (g2_point_kernel_eq_plane S m hd f hX).symm,
    f_I,hinner,hpoint,hfirst,hsecond,hradical,hrelative,hfirstK,hHe,hunique⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
