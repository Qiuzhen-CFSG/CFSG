module
public import Theory.GroupTheory.AutomorphismInvariantNormalKernel
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# The cyclic-orbit centralizer in Niles pushing-up

Let N_alpha be the largest alpha-invariant ambient normal subgroup inside S.
A supplement L whose commutator with W=Omega1 Z(N_alpha) has S-centralizer Q
identifies N_alpha with the intersection of all cyclic alpha-translates of Q.
The alpha-orbit span of that commutator lies in W and is normalized by L;
its centralizer is normal under both S and L, hence ambient-normal. Maximality
of N_alpha and centrality of W then give equality. The supplement and its
commutator-centralizer identity are supplied by the separate maximum-abelian
and natural-module arguments.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 7.6, printed p.62.
-/

public section
open Subgroup
open scoped Pointwise
namespace NilesRankOneKernel
variable {H : Type*} [Group H]

private theorem map_zpow_stable {G : Type*} [Group G]
    (α : MulAut G) (W : Subgroup G) (hW : W.map α.toMonoidHom = W) (n : ℤ) :
    W.map ((α ^ n).toMonoidHom) = W := by
  let P : Subgroup (MulAut G) := MulAction.stabilizer (MulAut G) W
  have hα : α ∈ P := by
    change W.map α.toMonoidHom = W
    exact hW
  have hh := P.zpow_mem hα n
  exact hh

private theorem orbit_join_fixed {G : Type*} [Group G] (α : MulAut G) (M : Subgroup G) :
    (⨆ n : ℤ, M.map ((α ^ n).toMonoidHom)).map α.toMonoidHom =
      ⨆ n : ℤ, M.map ((α ^ n).toMonoidHom) := by
  rw [Subgroup.map_iSup]
  have he (n : ℤ) : (M.map ((α ^ n).toMonoidHom)).map α.toMonoidHom =
      M.map ((α ^ (n+1)).toMonoidHom) := by
    rw [map_map]
    congr 1
    ext x
    change α ((α ^ n) x) = (α ^ (n+1)) x
    rw [zpow_add_one, ← Commute.self_zpow α n |>.eq]
    rfl
  simp_rw [he]
  apply le_antisymm
  · exact iSup_le (fun n => le_iSup_of_le (n+1) le_rfl)
  · apply iSup_le
    intro n
    simpa only [sub_add_cancel] using
      (le_iSup (fun m : ℤ => M.map ((α ^ (m+1)).toMonoidHom)) (n-1))

private theorem orbit_centralizer {G : Type*} [Group G]
    (α : MulAut G) (M : Subgroup G) :
    centralizer ((⨆ n : ℤ, M.map ((α ^ n).toMonoidHom) : Subgroup G) : Set G) =
      ⨅ n : ℤ, (centralizer (M : Set G)).map ((α ^ n).toMonoidHom) := by
  have hm (e : MulAut G) : (centralizer (M : Set G)).map e.toMonoidHom =
      centralizer (M.map e.toMonoidHom : Set G) := by
    apply le_antisymm (map_centralizer_le_centralizer_image _ _)
    intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
  simp_rw [hm]
  apply le_antisymm
  · exact le_iInf (fun n => centralizer_le (show M.map ((α ^ n).toMonoidHom) ≤ (⨆ n : ℤ, M.map ((α ^ n).toMonoidHom) : Subgroup G) from le_iSup (fun n : ℤ => M.map ((α ^ n).toMonoidHom)) n))
  · apply le_centralizer_iff.mpr
    apply iSup_le
    intro n
    exact le_centralizer_iff.mp (iInf_le _ n)

/-- The final cyclic-orbit centralizer argument of Niles Lemma 7.6.
The source's W, its commutator M=[W,L], and the supplement L are literal
subgroups; normality of the orbit intersection is proved, not assumed. -/
theorem invariantKernel_eq_orbit_inf_of_commutator
    (S : Subgroup H) (α : MulAut S) (Q W M : Subgroup S)
    [Q.Normal] [(Q.map S.subtype).Normal]
    (L : Subgroup H) (hgen : S ⊔ L = ⊤)
    (hW : W.map α.toMonoidHom = W)
    (hNW : invariantNormalKernel S α ≤ centralizer (W : Set S))
    (hMW : M ≤ W) (hCM : centralizer (M : Set S) = Q)
    (hcomm : ⁅W.map S.subtype, L⁆ ≤ M.map S.subtype) :
    invariantNormalKernel S α = ⨅ n : ℤ, Q.map ((α ^ n).toMonoidHom) := by
  let U : Subgroup S := ⨆ n : ℤ, M.map ((α ^ n).toMonoidHom)
  let C := centralizer (U : Set S)
  have hMU : M ≤ U := by
    have hh := le_iSup (fun n : ℤ => M.map ((α ^ n).toMonoidHom)) 0
    rw [zpow_zero] at hh
    change M.map (MonoidHom.id S) ≤ U at hh
    simpa only [Subgroup.map_id] using hh
  have hUW : U ≤ W := by
    apply iSup_le
    intro n
    exact (map_mono hMW).trans_eq (map_zpow_stable α W hW n)
  have hC : C = ⨅ n : ℤ, Q.map ((α ^ n).toMonoidHom) := by
    dsimp only [C,U]
    rw [orbit_centralizer,hCM]
  have hCQ : C ≤ Q := by
    calc
      C ≤ centralizer (M : Set S) := centralizer_le hMU
      _ = Q := hCM
  have hCN : C.Normal := by
    rw [hC]
    exact normal_iInf_normal (fun n =>
      (inferInstance : Q.Normal).map ((α ^ n).toMonoidHom) (α ^ n).surjective)
  have hSU : S ≤ normalizer (C.map S.subtype : Set H) := by
    have hh := C.le_normalizer_map S.subtype
    rw [C.normalizer_eq_top, ← MonoidHom.range_eq_map, S.range_subtype] at hh
    exact hh
  have hLU : L ≤ normalizer (U.map S.subtype : Set H) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono (map_mono hUW) le_rfl).trans (hcomm.trans (map_mono hMU))
  have hCe : C.map S.subtype = Q.map S.subtype ⊓
      centralizer (U.map S.subtype : Set H) := by
    apply le_antisymm
    · exact le_inf (map_mono hCQ) (map_centralizer_le_centralizer_image _ _)
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := hx.1
      refine ⟨a, ?_, rfl⟩
      intro u hu
      apply Subtype.ext
      exact hx.2 u (mem_map_of_mem S.subtype hu)
  have hLC : L ≤ normalizer (C.map S.subtype : Set H) := by
    rw [hCe]
    exact (le_inf le_normalizer_of_normal
      (hLU.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hambient : (C.map S.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← hgen]
    exact sup_le hSU hLC
  have hfix : C.map α.toMonoidHom = C := by
    change (centralizer (U : Set S)).map α.toMonoidHom = centralizer (U : Set S)
    have he : (centralizer (U : Set S)).map α.toMonoidHom =
        centralizer (U.map α.toMonoidHom : Set S) := by
      apply le_antisymm (map_centralizer_le_centralizer_image _ _)
      intro x hx
      refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
      intro y hy
      apply α.injective
      simpa only [map_mul, α.apply_symm_apply] using hx (α y) (mem_map_of_mem _ hy)
    rw [he,show U.map α.toMonoidHom = U from orbit_join_fixed α M]
  have hle := le_invariantNormalKernel S α C hambient hfix
  rw [← hC]
  exact le_antisymm (hNW.trans (centralizer_le hUW)) hle

/-- Central omega commutes with an injective group map. -/
theorem omegaCenterIn_map_injective {G D : Type*} [Group G] [Group D]
    (f : G →* D) (hf : Function.Injective f) (P : Subgroup G) :
    (omegaCenterIn P).map f = omegaCenterIn (P.map f) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨hP,hC,hp⟩ := (mem_omegaCenterIn_iff P x).mp hx
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨mem_map_of_mem f hP, ?_, ?_⟩
    · rintro z ⟨w,hw,rfl⟩
      simpa only [map_mul] using congrArg f (hC w hw)
    · rw [← map_pow,hp,map_one]
  · intro hy
    obtain ⟨hP,hC,hp⟩ := (mem_omegaCenterIn_iff _ _).mp hy
    obtain ⟨x,hx,rfl⟩ := hP
    refine ⟨x,(mem_omegaCenterIn_iff _ _).mpr ⟨hx,?_,?_⟩,rfl⟩
    · intro w hw
      apply hf
      simpa only [map_mul] using hC (f w) (mem_map_of_mem f hw)
    · apply hf
      simpa only [map_pow,map_one] using hp

/-- The orbit argument with the source's actual W=Omega1 Z(N_alpha).
Only the supplement and the centralizer of its actual commutator with W
remain: the maximum-abelian and natural-module arguments produce those. -/
theorem invariantKernel_eq_orbit_inf_of_omega_commutator
    (S : Subgroup H) (α : MulAut S) (Q : Subgroup S)
    [Q.Normal] [(Q.map S.subtype).Normal]
    (L : Subgroup H) (hgen : S ⊔ L = ⊤)
    (hCM : centralizer ((⁅(omegaCenterIn (invariantNormalKernel S α)).map S.subtype,
      L⁆).subgroupOf S : Set S) = Q) :
    invariantNormalKernel S α = ⨅ n : ℤ, Q.map ((α ^ n).toMonoidHom) := by
  let N := invariantNormalKernel S α
  let W := omegaCenterIn N
  have hW : W.map α.toMonoidHom = W := by
    rw [omegaCenterIn_map_injective _ α.injective,
      invariantNormalKernel_fixed]
  have hNW : N ≤ centralizer (W : Set S) := by
    apply le_centralizer_iff.mpr
    intro x hx
    exact ((mem_omegaCenterIn_iff N x).mp hx).2.1
  have hWN : (W.map S.subtype).Normal := by
    rw [omegaCenterIn_map_injective _ S.subtype_injective]
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    calc
      ⊤ = normalizer (N.map S.subtype : Set H) := (Subgroup.normalizer_eq_top (N.map S.subtype)).symm
      _ ≤ normalizer (omegaCenterIn (N.map S.subtype) : Set H) :=
        normalizer_le_normalizer_omegaCenterIn _
  have hcommW : ⁅W.map S.subtype,L⁆ ≤ W.map S.subtype :=
    le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal
  let M := (⁅W.map S.subtype,L⁆).subgroupOf S
  have hM : M.map S.subtype = ⁅W.map S.subtype,L⁆ :=
    map_subgroupOf_eq_of_le (hcommW.trans (map_subtype_le _))
  have hMW : M ≤ W := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hcommW hx
    exact S.subtype_injective he ▸ hy
  exact invariantKernel_eq_orbit_inf_of_commutator S α Q W M L hgen hW hNW
    hMW hCM hM.ge

end NilesRankOneKernel
