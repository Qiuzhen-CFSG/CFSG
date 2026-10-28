module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.SylowIntersection
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.TorusNormalizer
public import CFSG.Quasithin.Chapter5.Section03LinearSource.HallNormalizer

/-!
# Suzuki's actual Hall subgroup and exceptional cosets in the linear row

Start with the native split torus in the proved ambient completion. Its
normalizer intersection with the full original Sylow normalizer is an odd
Hall complement. The same endpoint reflections normalize that complement.
The local two-coset calculation and Hall conjugacy give precisely two
invariant central lines in each original root plane. Disjoint Sylows give
an involution in the Hall coset, and so does a root-plane intersection.
In the remaining case, the marked intersection line determines the other
Sylow center by unique root-plane incidence.

Every subgroup, Sylow and central line remains in the original group. The
whole common normalizer is retained, field four is included, and both native
comparison orientations use the same actual endpoint witnesses. This proves
the geometric and Hall-coset ingredients of Aschbacher–Smith F.4.49(1–2) and
the uniqueness step in (3), printed pp.298–299 of `refs/quasithin.pdf`.
The odd-product count and terminal ambient recognition follow separately.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
open Subgroup.OddHall CFSG.Quasithin.Chapter5.Section03LinearSource
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax


/-- The precise native torus is Hall in the original common Borel and has
trivial normalizer intersection with the original ambient Sylow. -/
theorem Preparation.linear_native_torus_hall
    (c : ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion F G)
    (hmid : c.middle.range=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)) :
    c.torusHom.range ≤ normalizer (T : Set G) ∧
      IsHallSubgroup oddPrimes (c.torusHom.range.subgroupOf c.middle.range) ∧
      Disjoint (T : Subgroup G) (normalizer (c.torusHom.range : Set G)) := by
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  have hf := d.hypothesisF11 h hH.1.1.2
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hCN : C ≤ normalizer (T : Set G) := by
    have hh := hf.commonBorel_normalizes_localSylow 0
    have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0
    change sourceS L H ≤ L at hs
    change C ≤ normalizer ((sourceS L H ⊓ L : Subgroup G) : Set G) at hh
    rwa [inf_eq_left.mpr hs,hST] at hh
  have hcore : C.pCoreIn 2 = (T : Subgroup G) := by
    obtain ⟨P,hP⟩ := hf.sylow_commonBorel
    apply le_antisymm ((pCoreIn_le_sylow C P).trans_eq (hP.trans hST))
    exact le_pCoreIn_of_normalizes T.isPGroup' (hST ▸ le_sup_right) hCN
  have hU : (((unipotent F).subgroupOf (borel F)).map c.middle)=(T : Subgroup G) := by
    rw [←BorelQuotient.twoCore_eq F hF]
    have hmap : (pCore 2 (borel F)).map c.middle=c.middle.range.pCoreIn 2 := by
      let e := MonoidHom.ofInjective c.middle_injective
      change _ = (pCore 2 c.middle.range).map c.middle.range.subtype
      rw [←pCore_map_iso 2 e,Subgroup.map_map]
      rfl
    rw [hmap,hmid]
    exact hcore
  have hq : 2<Nat.card F := by
    rw [hF,(d.linear_core_structure h hH hp F hm hF he).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  exact ⟨c.torus_le_middle.trans (hmid ▸ hCN),c.torus_hall hF,
    hU ▸ c.unipotent_torus_disjoint hF hq⟩

/-- The full torus stabilizer in the full Sylow normalizer is its odd Hall
complement, and both original native reflections normalize this same subgroup. -/
theorem Preparation.linear_native_full_hall
    (c : ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion F G)
    (i : Bool)
    (hleft : c.family i=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
    (hright : c.family (!i)=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (hmid : c.middle.range=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)) :
    let N := normalizer (T : Set G)
    let D := c.torusHom.range
    let B₀ := N ⊓ normalizer (D : Set G)
    D ≤ B₀ ∧ IsHallSubgroup oddPrimes (B₀.subgroupOf N) ∧ Odd (Nat.card B₀) ∧
      (N : Set G)=(T : Set G)*(B₀ : Set G) ∧
      (∀ j : Bool, c.weyl j ∈ normalizer (B₀ : Set G)) ∧
      N ⊓ normalizer (B₀ : Set G)=B₀ := by
  let N := normalizer (T : Set G)
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  let D := c.torusHom.range
  let B₀ := N ⊓ normalizer (D : Set G)
  change c.middle.range=C at hmid
  have hf := d.hypothesisF11 h hH.1.1.2
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hNI : N=normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
    d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax
  have hNPS (j : Fin 2) : N ≤ normalizer (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) j : Set G) := by
    rw [hNI]
    exact LinearCompletion.normalizes_parabolics L (residual H) (sourceS L H)
      (by rw [hST,←hNI]; exact le_rfl) j
  have hNP (j : Bool) : N≤normalizer (c.family j : Set G) := by
    cases i <;> cases j <;> simp only [Bool.not_false,Bool.not_true] at hleft hright <;>
      first | rw [hleft]; exact hNPS 0 | rw [hright]; exact hNPS 1
  have hNC : N≤normalizer (C : Set G) := by
    change N ≤ normalizer (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) : Set G)
    rw [←ChapterF.Source.lemma_F_1_3_6 hf]
    exact (le_inf (hNPS 0) (hNPS 1)).trans inf_normalizer_le_normalizer_inf
  have hCN : C≤N := by
    rw [hNI]
    exact le_inf (hf.commonBorel_normalizes_local 0) (hf.commonBorel_normalizes_local 1)
  obtain ⟨hDN,hDHall,hdis⟩ := d.linear_native_torus_hall h hH hp F hm hF he hmax c hmid
  have hDB : D≤B₀ := le_inf hDN D.le_normalizer
  have hDC : D≤C := c.torus_le_middle.trans_eq hmid
  have hHallC : IsHallSubgroup oddPrimes (D.subgroupOf C) := by
    change IsHallSubgroup oddPrimes (D.subgroupOf c.middle.range) at hDHall
    rwa [hmid] at hDHall
  obtain ⟨P,hP⟩ := hf.sylow_commonBorel
  have hprod : (N : Set G)=(T : Set G)*(B₀ : Set G) :=
    normal_sylow_frattini C (T : Subgroup G) N D hf.commonBorel_solvable
      (T : Subgroup G).le_normalizer hNC P (hP.trans hST) hDC hHallC
  have ho : Odd (Nat.card B₀) :=
    odd_of_disjoint_normalizer_sylow T B₀ inf_le_left (hdis.mono_right inf_le_right)
  have hsup : (T : Subgroup G) ⊔ B₀=N := by
    apply le_antisymm (sup_le (T : Subgroup G).le_normalizer inf_le_left)
    intro x hx
    have hx' : x∈(N : Set G) := hx
    rw [hprod] at hx'
    obtain ⟨t,ht,b,hb,rfl⟩ := hx'
    exact (T ⊔ B₀ : Subgroup G).mul_mem ((le_sup_left : (T : Subgroup G) ≤ (T : Subgroup G) ⊔ B₀) ht)
      ((le_sup_right : B₀ ≤ (T : Subgroup G) ⊔ B₀) hb)
  have hHall := oddHall_of_normalized_sup T.isPGroup' ho.coprime_two_left inf_le_left hsup
  have hq : 2<Nat.card F := by
    rw [hF,(d.linear_core_structure h hH hp F hm hF he).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  refine ⟨hDB,hHall,ho,hprod,?_,?_⟩
  · intro j
    exact c.weyl_normalizes_full_torus_stabilizer hq N (hmid ▸ hCN) hNP (hmid ▸ hNC) j
  · apply le_antisymm _ (le_inf inf_le_left B₀.le_normalizer)
    rintro x ⟨hxN,hxB⟩
    have hx' : x∈(N : Set G) := hxN
    rw [hprod] at hx'
    obtain ⟨t,ht,b,hb,rfl⟩ := hx'
    have htB : t ∈ normalizer (B₀ : Set G) := by
      have hh := (normalizer (B₀ : Set G)).mul_mem hxB
        ((normalizer _).inv_mem (B₀.le_normalizer hb))
      simpa only [mul_inv_cancel_right] using hh
    have htD : t ∈ normalizer (D : Set G) := by
      have hDCeq : D=B₀ ⊓ C := by
        change D=(N ⊓ normalizer (D : Set G)) ⊓ C
        rw [inf_right_comm,inf_eq_right.mpr hCN,←hmid]
        exact (c.middle_torus_normalizer_eq hq).symm
      rw [hDCeq]
      exact inf_normalizer_le_normalizer_inf ⟨htB,hNC ((T : Subgroup G).le_normalizer ht)⟩
    have ht1 := disjoint_def.mp hdis ht htD
    change t*b∈B₀
    rw [ht1,one_mul]
    exact hb

variable (c : ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion F G)
    (i : Bool)
    (hleft : c.family i=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
    (hright : c.family (!i)=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (hmid : c.middle.range=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
include hleft hright hmid

/-- In the disjoint-Sylow case the full normalizers intersect in the actual
full Hall complement, and its coset contains the swapping involution. -/
theorem Preparation.linear_hall_disjoint_coset
    (g : G)
    (hg : g∈normalizer ((normalizer (T : Set G) ⊓
      normalizer (c.torusHom.range : Set G) : Subgroup G) : Set G))
    (hdis : Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g)) :
    let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
    normalizer (T : Set G) ⊓ normalizer ((T : Subgroup G).conjBy g : Set G)=B₀ ∧
      ∃ w : G, orderOf w=2 ∧ w∈normalizer (B₀ : Set G) ∧
        (T : Subgroup G).conjBy w=(T : Subgroup G).conjBy g ∧ g⁻¹*w∈B₀ := by
  let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
  obtain ⟨_,hHall,_,_,_,hstab⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax
    c i hleft hright hmid
  have hBU : B₀≤normalizer ((T : Subgroup G).conjBy g : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom)
      (show B₀≤normalizer (T : Set G) from inf_le_left)).trans
      ((T : Subgroup G).le_normalizer_map _)
    have heq : B₀.map (MulAut.conj g).toMonoidHom=B₀ := mem_normalizer_iff_map_conj_eq.mp hg
    rwa [heq] at hh
  have hint := disjoint_sylow_normalizer_inter_eq_hall T (g • T) B₀ inf_le_left hBU hHall hdis
  have hgN : g∉normalizer (T : Set G) := by
    intro hh
    have heq : (T : Subgroup G).conjBy g=(T : Subgroup G) := mem_normalizer_iff_map_conj_eq.mp hh
    have hdd := hdis
    rw [heq] at hdd
    have htbot : (T : Subgroup G)=⊥ := disjoint_self.mp hdd
    obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
    have hzT := (d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax).le hz.1
    have hz1 := mem_bot.mp (htbot ▸ hzT)
    simp only [hz1,orderOf_one] at hz2
    omega
  obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  obtain ⟨w,hw,hTw,_,hwN⟩ := d.linear_disjoint_sylow_swap h hH hp F hm hF he hmax z hz2 hz g hgN hdis
  have hwB : w∈normalizer (B₀ : Set G) := by
    change normalizer (T : Set G) ⊓ normalizer ((T : Subgroup G).conjBy g : Set G)=B₀ at hint
    exact hint ▸ hwN
  have hgwT : g⁻¹*w∈normalizer (T : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (T : Subgroup G).conjBy (g⁻¹*w)=(T : Subgroup G)
    rw [←conjBy_conjBy,hTw,conjBy_conjBy,inv_mul_cancel,conjBy_one]
  refine ⟨hint,w,hw,hwB,hTw,?_⟩
  exact hstab.le ⟨hgwT,(normalizer _).mul_mem ((normalizer _).inv_mem hg) hwB⟩

/-- The full local normalizer preserves its native parabolic; its elements
factor through that parabolic and the actual common odd Hall subgroup. -/
theorem Preparation.linear_hall_local_layout
    (j : Bool) (k : Fin 2)
    (hjk : c.family j=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k) :
    let N := normalizer (T : Set G)
    let B₀ := N ⊓ normalizer (c.torusHom.range : Set G)
    c.family j ⊓ N=c.middle.range ∧
      normalizer (![L,residual H] k : Set G) ≤ normalizer (c.family j : Set G) ∧
      ∀ x∈normalizer (![L,residual H] k : Set G),
        ∃ p∈c.family j, ∃ b∈B₀, x=p*b := by
  let N := normalizer (T : Set G)
  let B₀ := N ⊓ normalizer (c.torusHom.range : Set G)
  have hf := d.hypothesisF11 h hH.1.1.2
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hS := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hNI : N=normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
    d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax
  have hLP : ![L,residual H] k ≤ c.family j := by
    rw [hjk]
    exact le_sup_left.trans le_sup_left
  have hNP : N≤normalizer (c.family j : Set G) := by
    rw [hjk,hNI]
    exact LinearCompletion.normalizes_parabolics L (residual H) (sourceS L H)
      (by rw [hST,←hNI]; exact le_rfl) k
  have hfactor (x : G) (hx : x∈normalizer (![L,residual H] k : Set G)) :
      ∃ l∈ ![L,residual H] k, ∃ b∈N, x=l*b := by
    rw [hNI]
    have hl := d.linear_normalizer_local_conditions h hH hp F hm hF he hmax
    fin_cases k
    · exact hl.factor_left x hx
    · exact hl.factor_right x hx
  obtain ⟨_,_,_,hprod,_,_⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax c i hleft hright hmid
  refine ⟨?_,?_,?_⟩
  · rw [hjk,hmid]
    have hh := hf.commonBorel_eq_normalizer k
    rw [inf_eq_left.mpr (hS k)] at hh
    simpa only [hST,Sylow.coe_coe] using hh.symm
  · intro x hx
    obtain ⟨l,hl,b,hb,rfl⟩ := hfactor x hx
    exact (normalizer _).mul_mem ((c.family j).le_normalizer (hLP hl)) (hNP hb)
  · intro x hx
    obtain ⟨l,hl,y,hy,hxy⟩ := hfactor x hx
    have hy' : y∈(normalizer (T : Set G) : Set G) := hy
    rw [hprod] at hy'
    obtain ⟨t,ht,b,hb,hyb⟩ := hy'
    refine ⟨l*t,(c.family j).mul_mem (hLP hl) (hLP ((hST ▸ hS k) ht)),b,hb,?_⟩
    rw [hxy,←hyb,mul_assoc]

/-- Every full local Hall-normalizer coset is one of the two original
reflection cosets, including q=4 and either comparison orientation. -/
theorem Preparation.linear_hall_local_cosets
    (j : Bool) (k : Fin 2)
    (hjk : c.family j=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k)
    (g : G) (hg : g∈normalizer (![L,residual H] k : Set G))
    (hgB : g∈normalizer ((normalizer (T : Set G) ⊓
      normalizer (c.torusHom.range : Set G) : Subgroup G) : Set G)) :
    let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
    g∈B₀ ∨ g*c.weyl j∈B₀ := by
  let N := normalizer (T : Set G)
  let D := c.torusHom.range
  let B₀ := N ⊓ normalizer (D : Set G)
  obtain ⟨hDB,_,_,_,hsB,_⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax c i hleft hright hmid
  obtain ⟨hPN,hMP,hfactor⟩ := d.linear_hall_local_layout h hH hp F hm hF he hmax c i hleft hright hmid j k hjk
  have hq : 2<Nat.card F := by
    rw [hF,(d.linear_core_structure h hH hp F hm hF he).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  have hDP : D=B₀ ⊓ c.family j := by
    change D=(N ⊓ normalizer (D : Set G)) ⊓ c.family j
    rw [inf_right_comm,inf_comm N (c.family j),hPN]
    exact (c.middle_torus_normalizer_eq hq).symm
  have hgD : g∈normalizer (D : Set G) := by
    rw [hDP]
    exact inf_normalizer_le_normalizer_inf ⟨hgB,hMP hg⟩
  obtain ⟨p,hpP,b,hb,hgpb⟩ := hfactor g hg
  have hpD : p∈normalizer (D : Set G) := by
    have hh := (normalizer (D : Set G)).mul_mem hgD ((normalizer _).inv_mem hb.2)
    simpa only [hgpb,mul_inv_cancel_right] using hh
  rcases c.endpoint_torus_normalizer hq j p hpP hpD with hp₀ | hp₁
  · left
    rw [hgpb]
    exact B₀.mul_mem (hDB hp₀) hb
  · right
    have hss : c.weyl j*c.weyl j=1 := by simpa only [←pow_two] using c.weyl_sq j
    have hsinv : (c.weyl j)⁻¹=c.weyl j := inv_eq_of_mul_eq_one_right hss
    have hconj : c.weyl j*b*c.weyl j∈B₀ := by
      simpa only [hsinv] using (mem_normalizer_iff.mp (hsB j) b).mp hb
    have hh := B₀.mul_mem (hDB hp₁) hconj
    change g*c.weyl j∈B₀
    rw [hgpb]
    have heq : (p*c.weyl j)*(c.weyl j*b*c.weyl j)=p*b*c.weyl j := by
      calc
        _ = p*(c.weyl j*c.weyl j)*b*c.weyl j := by group
        _ = _ := by rw [hss,mul_one]
    exact heq ▸ hh

/-- Exactly the two marked central lines can be invariant under the full
Hall subgroup in either original root plane. -/
theorem Preparation.linear_hall_invariant_root_line
    (j : Bool) (k : Fin 2)
    (hjk : c.family j=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k)
    (g : G)
    (hgQ : (centerIn (sourceS L H)).conjBy g ≤ (![L,residual H] k).pCoreIn 2)
    (hgB : (normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G) : Subgroup G) ≤
      normalizer ((centerIn (sourceS L H)).conjBy g : Set G)) :
    (centerIn (sourceS L H)).conjBy g=centerIn (sourceS L H) ∨
      (centerIn (sourceS L H)).conjBy g=(centerIn (sourceS L H)).conjBy (c.weyl j) := by
  let Z := centerIn (sourceS L H)
  let N := normalizer (T : Set G)
  let D := c.torusHom.range
  let B₀ := N ⊓ normalizer (D : Set G)
  have hNI : N=normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
    d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax
  have hZN : normalizer (Z : Set G)=N :=
    (d.linear_center_normalizer h hH hp F hm hF he hmax).trans hNI.symm
  obtain ⟨hDB,_,_,_,_,_⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax c i hleft hright hmid
  obtain ⟨hPN,_,_⟩ := d.linear_hall_local_layout h hH hp F hm hF he hmax c i hleft hright hmid j k hjk
  have hC : c.family j ⊓ normalizer (Z : Set G)=c.middle.range := by
    rw [hZN]
    exact hPN
  have hDP : D≤c.family j := by
    apply c.torus_le_middle.trans
    cases j
    · exact c.middle_le_left
    · exact c.middle_le_right
  have hDZ : D≤normalizer (Z : Set G) := by
    rw [hZN]
    exact hDB.trans inf_le_left
  have hsolv : Group.IsSolvable (c.family j ⊓ normalizer (Z : Set G) : Subgroup G) := by
    rw [hC,hmid]
    exact (d.hypothesisF11 h hH.1.1.2).commonBorel_solvable
  have hHall : IsHallSubgroup oddPrimes (D.subgroupOf (c.family j ⊓ normalizer (Z : Set G))) := by
    rw [hC]
    exact c.torus_hall hF
  have hq : 2<Nat.card F := by
    rw [hF,(d.linear_core_structure h hH hp F hm hF he).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  obtain ⟨a,ha,hag⟩ := d.linear_root_line_fusion h hH hp F hm hF he hmax k g hgQ
  have haP : a∈c.family j := by
    rw [hjk]
    exact (le_sup_left.trans le_sup_left : ![L,residual H] k ≤
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k) ha
  have hfix : D≤normalizer (Z.conjBy a : Set G) := by
    change Z.conjBy a=Z.conjBy g at hag
    rw [hag]
    exact hDB.trans hgB
  have hh := invariant_local_conjugate_eq (c.family j) Z D (c.weyl j) hDP hDZ hsolv
    hHall (c.weyl_sq j) (c.weyl_normalizes_torus j)
    (c.endpoint_torus_normalizer hq j) a haP hfix
  rwa [hag] at hh

/-- Suzuki's coset alternatives: a coset without an involution fixes the
original Sylow or has one of the two marked central-line intersections. -/
theorem Preparation.linear_hall_coset_alternatives
    (g : G)
    (hg : g∈normalizer ((normalizer (T : Set G) ⊓
      normalizer (c.torusHom.range : Set G) : Subgroup G) : Set G)) :
    let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
    g∈B₀ ∨ (∃ w : G, orderOf w=2 ∧ w*g⁻¹∈B₀) ∨
      ∃ j : Bool, (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g =
        (centerIn (sourceS L H)).conjBy (c.weyl j) ∧
        (centerIn (sourceS L H)).conjBy (c.weyl j)≠(centerIn (sourceS L H)).conjBy g := by
  let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
  obtain ⟨_,_,_,_,_,hstab⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax c i hleft hright hmid
  by_cases hgN : g∈normalizer (T : Set G)
  · exact Or.inl (hstab.le ⟨hgN,hg⟩)
  have hcos (j : Bool) (k : Fin 2)
      (hjk : c.family j=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k)
      (hgk : g∈normalizer (![L,residual H] k : Set G)) :
      ∃ w : G, orderOf w=2 ∧ w*g⁻¹∈B₀ := by
    have hh := d.linear_hall_local_cosets h hH hp F hm hF he hmax c i hleft hright hmid j k hjk g hgk hg
    have hh' : g*c.weyl j∈B₀ := hh.resolve_left (fun hb => hgN hb.1)
    have hss : c.weyl j*c.weyl j=1 := by simpa only [←pow_two] using c.weyl_sq j
    have hsinv : (c.weyl j)⁻¹=c.weyl j := inv_eq_of_mul_eq_one_right hss
    refine ⟨c.weyl j,?_,?_⟩
    · apply orderOf_eq_prime_iff.mpr
      refine ⟨c.weyl_sq j,?_⟩
      intro hh
      exact c.weyl_not_mem_middle j (hh ▸ c.middle.range.one_mem)
    · simpa only [mul_inv_rev,hsinv] using B₀.inv_mem hh'
  obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  rcases d.linear_sylow_intersection_trichotomy h hH hp F hm hF he hmax z hz2 hz g hgN with hd | hr | hl
  · obtain ⟨_,w,hw,_,_,hgw⟩ := d.linear_hall_disjoint_coset h hH hp F hm hF he hmax c i hleft hright hmid g hg hd.1
    right; left
    refine ⟨w,hw,?_⟩
    have hh := (mem_normalizer_iff.mp hg (g⁻¹*w)).mp hgw
    simpa only [mul_inv_cancel_left] using hh
  · obtain ⟨k,hk,_,_⟩ := hr
    have hgk := d.linear_root_plane_intersection_normalizer h hH hp F hm hF he hmax k g
      (hk ▸ (inf_le_right : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≤ (T : Subgroup G).conjBy g))
    right; left
    fin_cases k
    · exact hcos i 0 hleft hgk
    · exact hcos (!i) 1 hright hgk
  · obtain ⟨⟨a,ha⟩,hZ,hZg,_⟩ := hl
    have hBU : B₀≤normalizer ((T : Subgroup G).conjBy g : Set G) := by
      have hh := (map_mono (f := (MulAut.conj g).toMonoidHom)
        (show B₀≤normalizer (T : Set G) from inf_le_left)).trans
        ((T : Subgroup G).le_normalizer_map _)
      have heq : B₀.map (MulAut.conj g).toMonoidHom=B₀ := mem_normalizer_iff_map_conj_eq.mp hg
      rwa [heq] at hh
    have hBa : B₀≤normalizer ((centerIn (sourceS L H)).conjBy a : Set G) := by
      rw [←ha]
      exact (le_inf (show B₀≤normalizer (T : Set G) from inf_le_left) hBU).trans
        inf_normalizer_le_normalizer_inf
    have haT : (centerIn (sourceS L H)).conjBy a≤(T : Subgroup G) := ha ▸ inf_le_left
    obtain ⟨k,hk⟩ := d.linear_central_line_in_sylow h hH hp F hm hF he hmax a haT
    have hline (j : Bool)
        (hjk : c.family j=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k) :
        (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g=(centerIn (sourceS L H)).conjBy (c.weyl j) := by
      have hh := d.linear_hall_invariant_root_line h hH hp F hm hF he hmax c i hleft hright hmid j k hjk a hk hBa
      exact ha.trans (hh.resolve_left (fun heq => hZ (ha.trans heq)))
    right; right
    fin_cases k
    · exact ⟨i,hline i hleft,fun hh => hZg ((hline i hleft).trans hh)⟩
    · exact ⟨!i,hline (!i) hright,fun hh => hZg ((hline (!i) hright).trans hh)⟩

/-- A central-line intersection determines the other Sylow center. This is
the uniqueness step behind Suzuki's two exceptional Hall cosets. -/
theorem Preparation.linear_hall_line_case_center
    (j : Bool) (k : Fin 2)
    (hjk : c.family j=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k)
    (hjother : c.family (!j)=ChapterF.Source.parabolic ![L,residual H] (sourceS L H) (ChapterF.Source.other k))
    (g : G)
    (hg : g∈normalizer ((normalizer (T : Set G) ⊓
      normalizer (c.torusHom.range : Set G) : Subgroup G) : Set G))
    (hint : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g=
      (centerIn (sourceS L H)).conjBy (c.weyl j))
    (hne : (centerIn (sourceS L H)).conjBy (c.weyl j)≠
      (centerIn (sourceS L H)).conjBy g) :
    (centerIn (sourceS L H)).conjBy g=
      (centerIn (sourceS L H)).conjBy (c.weyl j*c.weyl (!j)) := by
  let Z := centerIn (sourceS L H)
  let Q := fun k : Fin 2 => (![L,residual H] k).pCoreIn 2
  let B₀ := normalizer (T : Set G) ⊓ normalizer (c.torusHom.range : Set G)
  let s := c.weyl j
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hNI := d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax
  have hZN : normalizer (Z : Set G)=normalizer (T : Set G) :=
    (d.linear_center_normalizer h hH hp F hm hF he hmax).trans hNI.symm
  have hZQ (l : Fin 2) : Z≤Q l := by
    have hh := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
    rw [←centerIn_eq_map_center] at hh
    fin_cases l
    · exact hh.le.trans inf_le_left
    · exact hh.le.trans inf_le_right
  have hQT (l : Fin 2) : Q l≤(T : Subgroup G) :=
    ((d.linear_core_structure h hH hp F hm hF he).2.2 l).2.2.trans_eq hST
  have hsM : s∈normalizer (![L,residual H] k : Set G) := by
    have hsP : s∈ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k := hjk ▸ c.weyl_mem j
    exact (normal_subgroupOf_iff_le_normalizer (show ![L,residual H] k≤
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) k from le_sup_left.trans le_sup_left)).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic k) hsP
  have hsQ : (Q k).conjBy s=Q k := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_characteristic_image (![L,residual H] k)
      (pCore 2 (![L,residual H] k)) hsM)
  have hsZ : Z.conjBy s≠Z := by
    intro hh
    have hsN : s∈normalizer (T : Set G) := hZN ▸ mem_normalizer_iff_map_conj_eq.mpr hh
    obtain ⟨hPN,_,_⟩ := d.linear_hall_local_layout h hH hp F hm hF he hmax c i hleft hright hmid j k hjk
    exact c.weyl_not_mem_middle j (hPN.le ⟨c.weyl_mem j,hsN⟩)
  have hUback : Z.conjBy (g⁻¹*s)≤(T : Subgroup G) := by
    have hUTg : Z.conjBy s≤(T : Subgroup G).conjBy g := hint ▸ inf_le_right
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hUTg
    change (Z.conjBy s).conjBy g⁻¹≤((T : Subgroup G).conjBy g).conjBy g⁻¹ at hh
    simpa only [conjBy_conjBy,inv_mul_cancel,conjBy_one] using hh
  obtain ⟨l,hl⟩ := d.linear_central_line_in_sylow h hH hp F hm hF he hmax (g⁻¹*s) hUback
  have hUQ : Z.conjBy s≤(Q l).conjBy g := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hl
    change (Z.conjBy (g⁻¹*s)).conjBy g≤(Q l).conjBy g at hh
    simpa only [conjBy_conjBy,mul_inv_cancel_left] using hh
  have heq := d.linear_root_plane_through_conjugate_center h hH hp F hm hF he hmax l s g hUQ
  have hlk : l≠k := by
    intro hh
    subst l
    have hQg : (Q k).conjBy g=Q k := heq.symm.trans hsQ
    have hQTg : Q k≤(T : Subgroup G).conjBy g := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (hQT k)
      change (Q k).conjBy g≤(T : Subgroup G).conjBy g at hh
      rwa [hQg] at hh
    have hZU : Z≤Z.conjBy s := (hZQ k).trans (hint ▸ le_inf (hQT k) hQTg)
    have hZZ : Z=Z.conjBy s := eq_of_le_of_card_ge hZU (by
      exact le_of_eq (card_map_of_injective (MulAut.conj s).injective))
    exact hsZ hZZ.symm
  have hlother : l=ChapterF.Source.other k := by
    fin_cases l <;> fin_cases k <;> simp_all [ChapterF.Source.other]
  subst l
  have hZgQ : Z.conjBy g≤(Q (ChapterF.Source.other k)).conjBy s := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (hZQ (ChapterF.Source.other k))
    exact hh.trans_eq heq.symm
  have hback : Z.conjBy (s⁻¹*g)≤Q (ChapterF.Source.other k) := by
    have hh := map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) hZgQ
    change (Z.conjBy g).conjBy s⁻¹≤((Q (ChapterF.Source.other k)).conjBy s).conjBy s⁻¹ at hh
    simpa only [conjBy_conjBy,inv_mul_cancel,conjBy_one] using hh
  obtain ⟨_,_,_,_,hsB,_⟩ := d.linear_native_full_hall h hH hp F hm hF he hmax c i hleft hright hmid
  have hxB : s⁻¹*g∈normalizer (B₀ : Set G) :=
    (normalizer _).mul_mem ((normalizer _).inv_mem (hsB j)) hg
  have hBZ : B₀≤normalizer (Z : Set G) := by rw [hZN]; exact inf_le_left
  have hfix : B₀≤normalizer (Z.conjBy (s⁻¹*g) : Set G) := by
    have hh := (map_mono (f := (MulAut.conj (s⁻¹*g)).toMonoidHom) hBZ).trans
      (Z.le_normalizer_map _)
    have hmB : B₀.map (MulAut.conj (s⁻¹*g)).toMonoidHom=B₀ := mem_normalizer_iff_map_conj_eq.mp hxB
    rwa [hmB] at hh
  have hcases := d.linear_hall_invariant_root_line h hH hp F hm hF he hmax c i hleft hright hmid
    (!j) (ChapterF.Source.other k) hjother (s⁻¹*g) hback hfix
  have hother : Z.conjBy (s⁻¹*g)=Z.conjBy (c.weyl (!j)) := by
    apply hcases.resolve_left
    intro hz
    have hh := congrArg (fun U : Subgroup G => U.conjBy s) hz
    rw [conjBy_conjBy,mul_inv_cancel_left] at hh
    exact hne hh.symm
  have hh := congrArg (fun U : Subgroup G => U.conjBy s) hother
  simpa only [conjBy_conjBy,mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
