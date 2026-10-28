module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModuleFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SingularGeometrySource
/-!
# Nonsingular vectors and the distinguished involution class

Conjugation inside the block moves a core vector into the Sylow center.
Orthogonal invariance excludes the opposite singular center, while the
nonradical condition excludes the block center. The resulting vector lies
in the distinguished torus orbit Δ.

Source: Aschbacher–Smith, the module geometry in Lemma 2.4.20 and its use
in the odd half-degree branch of Lemma 2.4.24(2).
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_nonsingular_nonradical_fused_delta
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S:Subgroup d.H).map d.H.subtype)
    (hxB : x∈normalizer (c.hall:Set G))
    {b : MulAut (d.block.map d.H.subtype)}
    (e : ChapterC.OrthogonalInvolutionCoordinates (d.block.map d.H.subtype) n b)
    (u : pCore 2 (d.block.map d.H.subtype))
    (huform : Representation.SL2OrthogonalCover.form (e.core u).toAdd≠0)
    (hurad : (e.core u).toAdd∉(Representation.SL2OrthogonalCover.form (F:=e.F)).polarBilin.ker)
    (v : G) (hv : v∈distinguishedDelta d x) : IsConj ((u:d.block.map d.H.subtype):G) v := by
  let L := d.block.map d.H.subtype
  have huU : ((u:L):G)∈sourceModule L := by
    have hu' : (u:L)∈ChapterC.blockU L := by
      rw [←source_block_core_eq_module d hG T hST hsingle]
      exact u.property
    exact mem_map_of_mem L.subtype hu'
  obtain ⟨l,hlL,hlA⟩ := source_module_fused_into_sylow_center d hG T hST hsingle hL hM hTM hunique ((u:L):G) huU
  let lL : L := ⟨l,hlL⟩
  let w := MulAut.conjNormal lL u
  have hwval : ((w:L):G)=l*((u:L):G)*l⁻¹ := rfl
  have hwform : Representation.SL2OrthogonalCover.form (e.core w).toAdd≠0 := by
    change Representation.SL2OrthogonalCover.form (e.core (MulAut.conjNormal lL u)).toAdd≠0
    rw [e.conjugation_equivariant,Representation.SL2OrthogonalCover.form_invariant]
    exact huform
  have hwDelta : ((w:L):G)∈distinguishedDelta d x := by
    refine ⟨hlA,?_,?_⟩
    · intro hwZ
      rw [distinguishedZ_of_center_ne_bot d hz] at hwZ
      have hwC : (w:L)∈center L := (mem_map_iff_mem L.subtype_injective).mp hwZ
      have huC : (u:L)∈center L := by
        have hh := (inferInstance : (center L).Normal).conj_mem (w:L) hwC lL⁻¹
        change lL⁻¹*(lL*(u:L)*lL⁻¹)*(lL⁻¹)⁻¹∈center L at hh
        simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
      exact hurad (e.center_mem_radical u huC)
    · intro hwW
      exact hwform (source_outside_center_singular d hG T hST hsingle hL hM hTM hunique c hz x hxT hxS e w hwW)
  obtain ⟨k,hk,he⟩ := source_distinguished_delta_transitive d hG T hST hsingle hL hM hTM hunique c hz x hxT hxS hxB ((w:L):G) hwDelta v hv
  exact (isConj_iff.mpr ⟨l,hwval.symm⟩).trans (isConj_iff.mpr ⟨k,he⟩)
private theorem nonsingular_radical_is_central
    {L : Type*} [Group L] {n : ℕ} {a : MulAut L}
    (e : ChapterC.OrthogonalInvolutionCoordinates L n a) (u : pCore 2 L)
    (hu : (e.core u).toAdd∈(Representation.SL2OrthogonalCover.form (F:=e.F)).polarBilin.ker) :
    (u:L)∈center L := by
  rw [←Representation.SL2OrthogonalCover.fixed_radical] at hu
  rw [Subgroup.mem_center_iff]
  intro l
  have he : MulAut.conjNormal l u=u := by
    apply e.core.injective
    apply Multiplicative.toAdd.injective
    rw [e.conjugation_equivariant]
    exact hu _
  have hh := congrArg (fun v:pCore 2 L=>v.val*l) he
  simpa only [MulAut.conjNormal_apply,MulEquiv.coe_mk,Subgroup.coe_mk,
    mul_assoc,inv_mul_cancel,mul_one] using hh

theorem source_nonsingular_noncentral_fused_delta
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S:Subgroup d.H).map d.H.subtype)
    (hxB : x∈normalizer (c.hall:Set G))
    {b : MulAut (d.block.map d.H.subtype)}
    (e : ChapterC.OrthogonalInvolutionCoordinates (d.block.map d.H.subtype) n b)
    (u : pCore 2 (d.block.map d.H.subtype))
    (huform : Representation.SL2OrthogonalCover.form (e.core u).toAdd≠0)
    (hucenter : (u:d.block.map d.H.subtype)∉center (d.block.map d.H.subtype))
    (v : G) (hv : v∈distinguishedDelta d x) : IsConj ((u:d.block.map d.H.subtype):G) v := by
  exact source_nonsingular_nonradical_fused_delta d hG T hST hsingle hL hM hTM hunique
    c hz x hxT hxS hxB e u huform (fun h=>hucenter (nonsingular_radical_is_central e u h)) v hv
end CFSG.Quasithin.Chapter2.LinearShadows.Single
