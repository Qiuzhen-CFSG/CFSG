module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCore
public import Theory.GroupTheory.SylowNormalPairFusion
public import Theory.GroupTheory.ElementSubgroupSylowIncidence

/-!
# Fusion and root transitivity for the original elementary cores

The two T-normal elementary sixteen-groups A₁,Q₂ cannot be exchanged by
the odd quotient N_G(T)/T. Burnside fusion excludes ambient conjugacy.
The nine-root count distinguishes A₂ from both five-root groups. Thus the
four-member local list reduces incidence to a single centralizer orbit,
giving transitivity of N_G(Aᵢ) on the roots in Aᵢ.

Source: Aschbacher--Smith F.5.4(4), printed p.301. The explicit local list
and its normal members are the finite-model inputs; all ambient fusion is
proved here from the original `FusionFacts`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)

omit [Finite G] in
/-- Ambient conjugation preserves the number of marked-class elements in a subgroup. -/
theorem classIntersection_card_conj (x : G) (B : Subgroup G) (g : G) :
    Nat.card (classIntersection x (B.conjBy g)) = Nat.card (classIntersection x B) := by
  let e := B.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let e' : classIntersection x B ≃ classIntersection x (B.conjBy g) :=
    e.toEquiv.subtypeEquiv (fun b => by
      change IsConj x b.val ↔ IsConj x (MulAut.conj g b.val)
      exact ⟨fun h => h.trans (isConj_iff.mpr ⟨g,rfl⟩),
        fun h => h.trans (isConj_iff.mpr ⟨g,rfl⟩).symm⟩)
  exact (Nat.card_congr e').symm

include hf in
/-- Burnside fusion separates the two original T-normal elementary cores. -/
theorem normalizer_point_not_conjugate_Q
    (hA : Source.sylowImage c i ≤ normalizer (A c i false : Set G))
    (hQ : Source.sylowImage c i ≤ normalizer (Q c i true : Set G))
    (hne : A c i false ≠ Q c i true)
    (hlocal : ∀ B : Subgroup G, B ≤ Source.sylowImage c i →
      IsElementaryAbelian 2 B → Nat.card B = 16 →
      Source.sylowImage c i ≤ normalizer (B : Set G) → B = A c i false ∨ B = Q c i true) :
    ∀ g : G, (A c i false).conjBy g ≠ Q c i true := by
  obtain ⟨S,hP⟩ := hf.sylow
  apply S.not_conjugate_of_normalizer_pair (A c i false) (Q c i true)
    (hP ▸ hA) (hP ▸ hQ) hne
  intro n hN
  have he : (Source.sylowImage c i).map (MulAut.conj n).toMonoidHom =
      Source.sylowImage c i := by
    rw [← hP]
    exact mem_normalizer_iff_map_conj_eq.mp hN
  have hAT : A c i false ≤ Source.sylowImage c i :=
    (normalizer_A_le_TfImage c i z t hf false).trans (by rw [TfImage_eq]; exact inf_le_left)
  let := hf.A_elementary false
  apply hlocal _
  · exact (map_mono hAT).trans he.le
  · exact IsElementaryAbelian.map _
  · rw [card_map_of_injective (MulAut.conj n).injective,hf.A_card]
  · rw [← he]
    exact (map_mono hA).trans ((A c i false).le_normalizer_map (MulAut.conj n).toMonoidHom)

include hf in
/-- The original normalizer is transitive on the root-class intersection.
The remaining premises are the literal four-member local family and its two
T-normal members, produced by the marked Sylow calculation. -/
theorem normalizer_root_transitive_of_family (y : G) (hy : y ∈ Source.sylowImage c i)
    (hA : Source.sylowImage c i ≤ normalizer (A c i false : Set G))
    (hQ : Source.sylowImage c i ≤ normalizer (Q c i true : Set G))
    (hne : A c i false ≠ Q c i true)
    (hnormal : ∀ B : Subgroup G, B ≤ Source.sylowImage c i →
      IsElementaryAbelian 2 B → Nat.card B = 16 →
      Source.sylowImage c i ≤ normalizer (B : Set G) → B = A c i false ∨ B = Q c i true)
    (hfamily : ∀ B : Subgroup G, B ≤ Source.sylowImage c i →
      IsElementaryAbelian 2 B → Nat.card B = 16 →
      B = A c i false ∨ B = A c i true ∨ B = (A c i true).conjBy y ∨ B = Q c i true) :
    ∀ b, ∀ x ∈ A c i b, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z) = x := by
  obtain ⟨S,hP⟩ := hf.sylow
  have hPC : (S : Subgroup G) ≤ centralizer ({rootElement c i z} : Set G) := by
    rw [hP,hf.root_centralizer]
    exact sylowImage_le_M c i false
  have hyC : y ∈ centralizer ({rootElement c i z} : Set G) := hPC (hP.symm ▸ hy)
  have hnf := normalizer_point_not_conjugate_Q c i z t hf hA hQ hne hnormal
  intro b
  let := hf.A_elementary b
  apply S.normalizer_transitive_of_local_incidence (A c i b) (rootElement c i z)
    (IsElementaryAbelian.isPGroup 2 (A c i b))
    (fun a ha d hd => congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A c i b) ⟨d,hd⟩)) hPC
  intro g hg
  have hgc := classIntersection_card_conj (rootElement c i z) (A c i b) g
  have hge : IsElementaryAbelian 2 ((A c i b).conjBy g) := IsElementaryAbelian.map _
  have hcard : Nat.card ((A c i b).conjBy g) = 16 := by
    rw [conjBy,card_map_of_injective (MulAut.conj g).injective,hf.A_card]
  rcases hfamily _ (hP ▸ hg) hge hcard with he | he | he | he
  · cases b
    · exact ⟨1,one_mem _,by rw [conjBy_one,he]⟩
    · rw [he,hf.root_class_A_point,hf.root_class_A_plane] at hgc
      omega
  · cases b
    · rw [he,hf.root_class_A_plane,hf.root_class_A_point] at hgc
      omega
    · exact ⟨1,one_mem _,by rw [conjBy_one,he]⟩
  · cases b
    · rw [he,classIntersection_card_conj,hf.root_class_A_plane,hf.root_class_A_point] at hgc
      omega
    · exact ⟨y,hyC,he.symm⟩
  · cases b
    · exact (hnf g he).elim
    · rw [he,hf.root_class_Q_plane,hf.root_class_A_plane] at hgc
      omega

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
