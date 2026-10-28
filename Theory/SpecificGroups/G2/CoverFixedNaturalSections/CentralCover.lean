module

public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.RadicalAbelian
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Perfectness
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual

/-!
# Abelian core subgroups in central covers of the G₂ local group

The image of an abelian normal subgroup of the two-core lies in the
highest-root group by the root-action calculation. This centralizes the
whole local group. A two-perfect covering group is perfect because its
kernel is a two-group and its local quotient is perfect. Centralizers of
perfect groups lift through central kernels, so the original abelian
subgroup is central as well.

The actual ambient conjugation section therefore has trivial action.
Surjectivity onto SL₂(4) contradicts the absence of nonzero fixed vectors
in its binary natural module. The actor map and section coordinates are
retained literally; no kernel size or splitting is assumed.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071, using the local radical
of F.1.11–12, printed pp.262–264.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped IsMulCommutative
namespace Atlas.G2.CoverFixedNaturalSections
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem abelian_core_le_center_of_cover {A : Type*} [Group A] [Finite A]
    (hq : 2 < Nat.card F) (hp : IsPPerfect 2 A)
    (f : A →* local₁ (F := F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center A) (hk : IsPGroup 2 f.ker)
    (B : Subgroup A) [B.Normal] [IsMulCommutative B] (hB : B ≤ pCore 2 A) :
    B ≤ center A := by
  let : Group.IsPerfect (local₁ (F := F)) := local₁_isPerfect hq
  let : Group.IsPerfect A := hp.isPerfect_of_surjective_pGroup_kernel f hf hk
  let C := (B.map f).map (local₁ (F := F)).subtype
  have hC : C ≤ radical₁ := by
    rw [← local₁_pCore]
    apply map_mono
    apply (map_mono hB).trans
    exact le_sSup ⟨Subgroup.Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  let : (B.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hn : local₁ (F := F) ≤ normalizer (C : Set (Model F)) := by
    have h := (B.map f).le_normalizer_map (local₁ (F := F)).subtype
    rw [normalizer_eq_top_iff.mpr (inferInstance : (B.map f).Normal),
      ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  have hhigh := abelian_normalized_radical_le_highestRoot hq C hC hn
    (fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x,hx⟩ : C) ⟨y,hy⟩))
  have hcent : B ≤ (centralizer ((⊤ : Subgroup A).map f : Set (local₁ (F := F)))).comap f := by
    intro b hb
    change f b ∈ centralizer ((⊤ : Subgroup A).map f : Set (local₁ (F := F)))
    rw [mem_centralizer_iff]
    intro y _
    obtain ⟨a,ha⟩ := hhigh (mem_map_of_mem _ (mem_map_of_mem f hb))
    apply Subtype.ext
    change (y : Model F) * (f b : Model F) = (f b : Model F) * y
    change rootA a.toAdd = (f b : Model F) at ha
    rw [← ha]
    exact mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA a.toAdd y.property)
  rw [comap_centralizer_map_eq_of_perfect f ⊤ (hc.trans (center_le_centralizer _)),
    coe_top, centralizer_univ] at hcent
  exact hcent

theorem not_naturalSection_of_cover {D : Type*} [Group D] [Finite D]
    (hq : 2 < Nat.card F) (R B E : Subgroup D)
    (hp : IsPPerfect 2 R) (f : R →* local₁ (F := F))
    (hf : Function.Surjective f) (hc : f.ker ≤ center R) (hk : IsPGroup 2 f.ker)
    [IsElementaryAbelian 2 B] (hB : B ≤ R.pCoreIn 2)
    (q : R →* Representation.SL2FourNatural.SL) (hqsur : Function.Surjective q) :
    ¬ Nonempty (Representation.BinaryConjugationSection R B E
      (Representation.SL2FourNatural.naturalRepresentation.comp q)) := by
  rintro ⟨s⟩
  let B' := B.subgroupOf R
  let : B'.Normal := normal_subgroupOf_of_le_normalizer s.normalized
  have hB' : B' ≤ pCore 2 R := by
    intro b hb
    obtain ⟨x,hx,he⟩ := hB hb
    exact (Subtype.ext he : x = b) ▸ hx
  have hcent := abelian_core_le_center_of_cover hq hp f hf hc hk B' hB'
  have hfixed (v : Representation.SL2FourNatural.V) : v = 0 := by
    apply Representation.SL2FourNatural.natural_fixed_eq_zero v
    intro g
    obtain ⟨r,hr⟩ := hqsur g
    obtain ⟨b,hb⟩ := s.onto (Multiplicative.ofAdd v)
    have hcb : (r : D) * b * (r : D)⁻¹ = b := by
      have hh := mem_center_iff.mp (hcent (show (⟨b,s.section_le b.property⟩ : R) ∈ B' from b.property)) r
      have he := congrArg Subtype.val hh
      change (r : D) * b = b * r at he
      rw [he, mul_inv_cancel_right]
    have hh := s.equivariant r b
    have hsub : (⟨(r : D) * b * (r : D)⁻¹,
        (mem_normalizer_iff.mp (s.normalized r.property) b).mp b.property⟩ : B) = b :=
      Subtype.ext hcb
    rw [hsub] at hh
    change (s.coordinates b).toAdd = Representation.SL2FourNatural.action (q r) (s.coordinates b).toAdd at hh
    simpa only [hb, hr, toAdd_ofAdd] using hh.symm
  have hz := congrFun (hfixed ![1,0]) 0
  exact one_ne_zero hz
end Atlas.G2.CoverFixedNaturalSections
