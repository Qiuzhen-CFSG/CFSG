module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Action
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Stabilizer factorization on the point-radical omega center

Write Y=N_G(R₁), M=N_G(L), P=T∩L and Z₁=Ω₁(Z(R₁)). The fixed-line
and center identities imply P≤C_G(Z₁). Thus P is a Sylow subgroup of
K=L∩C_G(Z₁)∩Y, which is normal in M∩Y. Relative Frattini reduces M∩Y
to K and the normalizer of P. The latter normalizes the solvable Cartan
normalizer B=N_L(P). Hall conjugacy in B supplies the remaining factorization
by P and N_G(X). Restricting to Y gives exactly the cover modulo C_Y(Z₁)
needed to normalize the Cartan image in the Goldschmidt–O'Nan action.

The fixed-line and center identities retain their original source meanings.
No normality of X in M∩Y is asserted before taking the centralizer quotient.
Source: Aschbacher–Smith, 11.1.5, printed p.766, the Cartan–TI paragraph.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped Pointwise IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G]

private theorem restrict_sylow {L K : Subgroup G} (hKL : K ≤ L)
    (P : Sylow 2 L) (hPK : (P : Subgroup L).map L.subtype ≤ K) :
    ∃ Q : Sylow 2 K, (Q : Subgroup K).map K.subtype = (P : Subgroup L).map L.subtype := by
  have hp : (P : Subgroup L) ≤ K.subgroupOf L := by
    intro p hp
    exact hPK (mem_map_of_mem L.subtype hp)
  let e := subgroupOfEquivOfLe hKL
  let Q := (P.subtype hp).mapSurjective
    (f := e.toMonoidHom) e.surjective
  refine ⟨Q, ?_⟩
  apply le_antisymm
  · rintro _ ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p.val, hp, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨e ⟨p, hPK (mem_map_of_mem L.subtype hp)⟩,
      ⟨⟨p, hPK (mem_map_of_mem L.subtype hp)⟩, hp, rfl⟩, rfl⟩

variable {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} {c : Coordinates D F}

/-- The literal Cartan normalizer is solvable: its 2-core is nilpotent and
its quotient is the product of the two scalar tori. -/
theorem cartanNormalizer_solvable (c : Coordinates D F) :
    Group.IsSolvable (cartanNormalizer T L) := by
  let B := cartanNormalizer T L
  let e := c.cartanNormalizerQuotientEquiv
  have : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
  have : Group.IsSolvable (B ⧸ pCore 2 B) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr
    ⟨inferInstance, inferInstance⟩

/-- Both summands of the corrected center identity are centralized by T∩L. -/
theorem innerSylow_centralizes_omegaCenter (f : InvariantFlag c)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L) :
    (T : Subgroup G) ⊓ L ≤ centralizer (radicalOmegaCenter (f.Ri 0) : Set G) := by
  apply le_centralizer_iff.mpr
  rw [hcenter]
  apply sup_le
  · rw [hfixed]
    exact inf_le_right.trans (centralizer_le sylow_intersection_le_sourceTL)
  · exact inf_le_right.trans (centralizer_le inf_le_right)

/-- The actual Y∩M stabilizer is covered by C_Y(Z₁) and N_Y(X).
This is the relative cover consumed by `chosen_normal_in_stabilizer`. -/
theorem stabilizer_cover_of_fixed_line
    (f : InvariantFlag c) {X : Subgroup G} (hX : IsCartan T L X)
    (hXY : X ≤ normalizer (f.Ri 0 : Set G))
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L) :
    (normalizer (L : Set G)).subgroupOf (normalizer (f.Ri 0 : Set G)) ≤
      kernel (f.Ri 0) ⊔ normalizer (X.subgroupOf (normalizer (f.Ri 0 : Set G)) : Set _) := by
  let Y := normalizer (f.Ri 0 : Set G)
  let H := normalizer (L : Set G) ⊓ Y
  let C := centralizer (radicalOmegaCenter (f.Ri 0) : Set G)
  let K := (L ⊓ C) ⊓ Y
  let P := (T : Subgroup G) ⊓ L
  let B := cartanNormalizer T L
  let N := H ⊓ normalizer (P : Set G)
  have hPY : P ≤ Y := inf_le_left.trans (sylow_normalizes_Ri f 0)
  have hPC : P ≤ C := innerSylow_centralizes_omegaCenter f hfixed hcenter
  have hPK : P ≤ K := le_inf (le_inf inf_le_right hPC) hPY
  have hKH : K ≤ H := le_inf ((inf_le_left.trans inf_le_left).trans L.le_normalizer) inf_le_right
  have hHK : H ≤ normalizer (K : Set G) :=
    (le_inf ((le_inf inf_le_left
      (inf_le_right.trans ((normalizes_omegaCenter (f.Ri 0)).trans
        (normalizer_le_normalizer_centralizer _)))).trans inf_normalizer_le_normalizer_inf)
      (inf_le_right.trans Y.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hP : (c.innerSylow : Subgroup L).map L.subtype = P := by
    rw [c.innerSylow_coe, subgroupOf_map_subtype]
  obtain ⟨Q, hQ⟩ := restrict_sylow (show K ≤ L from inf_le_left.trans inf_le_left)
    c.innerSylow (hP ▸ hPK)
  have hfrat : H = K ⊔ N := relative_frattini hKH hHK Q (hQ.trans hP)
  have hNB : N ≤ normalizer (B : Set G) := by
    dsimp only [B]
    rw [cartanNormalizer_eq_intersection_normalizer]
    exact (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hPH : P ≤ H := le_inf (inf_le_right.trans L.le_normalizer) hPY
  have hPN : P ≤ N := le_inf hPH P.le_normalizer
  have hHall := OddHall.normal_sylow_frattini B
    ((cartanSylow c : Subgroup B).map B.subtype) N X
    (cartanNormalizer_solvable c)
    ((show (cartanSylow c : Subgroup B).map B.subtype ≤ P from by
      rintro _ ⟨p, hp, rfl⟩
      exact cartanSylow_le_intersection p hp).trans hPN)
    hNB (cartanSylow c) rfl hX.1 hX.2
  have hH : H ≤ (C ⊓ Y) ⊔ (normalizer (X : Set G) ⊓ Y) := by
    rw [hfrat]
    apply sup_le
    · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans le_sup_left
    · intro n hn
      have he : n ∈ (N : Set G) := hn
      rw [hHall] at he
      obtain ⟨p, ⟨q, hq, rfl⟩, y, hy, rfl⟩ := he
      exact mul_mem ((le_sup_left : C ⊓ Y ≤ _) ⟨hPC (cartanSylow_le_intersection q hq),
        hPY (cartanSylow_le_intersection q hq)⟩)
        ((le_sup_right : normalizer (X : Set G) ⊓ Y ≤ _) ⟨hy.2, hy.1.1.2⟩)
  intro y hy
  have hh : y.val ∈ (C ⊓ Y) ⊔ (normalizer (X : Set G) ⊓ Y) := hH ⟨hy, y.property⟩
  have hh' : y ∈ ((C ⊓ Y) ⊔ (normalizer (X : Set G) ⊓ Y)).subgroupOf Y := hh
  rw [subgroupOf_sup inf_le_right inf_le_right] at hh'
  have hC : (C ⊓ Y).subgroupOf Y = kernel (f.Ri 0) := by
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, z.property⟩⟩
  have hN : (normalizer (X : Set G) ⊓ Y).subgroupOf Y =
      normalizer (X.subgroupOf Y : Set Y) := by
    rw [← subgroupOf_normalizer_eq hXY]
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, z.property⟩⟩
  rwa [hC, hN] at hh'

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
