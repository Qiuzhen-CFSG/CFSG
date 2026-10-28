module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreIntersection
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PlaneFusion
public import Theory.GroupTheory.NormalizerAction


/-!
# Exact normalizers of the maximal-core cubic plane

In the order-243 branch of the original G₂(3) configuration, let E be the
marked cubic plane and U its canonical elementary extension of order81.
The full centralizer of E has order162, so its marked involution is Sylow.
Sylow conjugacy adjusts every element of N_G(E) into the original H.
The proved H-fusion theorem then makes its action on E identity or inversion.
Consequently N_G(E) is U times the original Klein four torus, with trivial
intersection, order324, and three-core exactly U.

The fixed subgroup C_U(z) is E. Hence C_{N_G(U)}(z) is E times the same
torus, of order36. Coprime centralizer lifting identifies the centralizer
of the marked involution in the faithful quotient N_G(U)/C_G(U) with the
actual torus. Here C_G(U)=U has already been proved, so this is the literal
normalizer quotient by U, with no substituted residual convention.

These are deductions from Aschbacher–Smith I.4(G1)–(G2), printed p.417,
refs/quasithin.pdf, PDF p.428, continuing the marked centralizer analysis
of Fong–Wong §3B. They do not exclude the strongly-three-embedded branch
or construct the Atlas G₂(3) equivalence. Chapter14MaximalNormalizer applies
them to SourceLocalData while preserving the original M-cubic and both cores.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

private theorem local_plane_scalar (t : CubicTorus c) (g : G) (hg : g∈c.H)
    (hgN : g∈normalizer ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G)) :
    (∀ a∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G), MulAut.conj g a=a) ∨
    (∀ a∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G), MulAut.conj g a=a⁻¹) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let : IsElementaryAbelian 3 E := (cubic_plane_data c t.x t.y t.x_order t.y_order).1
  let : CommGroup E := IsMulCommutative.instCommGroup
  let f : E →* G := (MulAut.conj g).toMonoidHom.comp E.subtype
  let A := f.eqLocus E.subtype
  let B := f.eqLocus (E.subtype.comp (invMonoidHom : E →* E))
  have hall : ((⊤:Subgroup E):Set E) ⊆ (A:Set E) ∪ (B:Set E) := by
    intro a _
    have ha : MulAut.conj g (a:G)∈E := (hgN (a:G)).mp a.property
    exact (t.plane_fusion_in_H_iff (a:G) (MulAut.conj g (a:G)) a.property ha).mp ⟨g,hg,rfl⟩
  rcases SubgroupClass.subset_union.mp hall with h|h
  · exact Or.inl (fun a ha => h (show (⟨a,ha⟩:E)∈(⊤:Subgroup E) from trivial))
  · exact Or.inr (fun a ha => h (show (⟨a,ha⟩:E)∈(⊤:Subgroup E) from trivial))

private theorem maximal_plane_normalizer_adjust (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243)
    (g : G) (hg : g∈normalizer ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G)) :
    ∃ q : G, q∈Subgroup.centralizer
      ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G) ∧ q*g∈c.H := by
  classical
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let C := Subgroup.centralizer (E:Set G)
  have hzC : (t.z:G)∈C := by
    intro a ha
    have hEH : E≤c.H := sup_le (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property)
    exact mem_centralizer_singleton_iff.mp (t.centralizer ▸ hEH ha)
  let z : C := ⟨t.z,hzC⟩
  have hz : orderOf z=2 := (orderOf_coe z).symm.trans ((orderOf_coe t.z).trans t.z_order)
  have hi : (zpowers z).index=81 := by
    have hh := (zpowers z).card_mul_index
    rw [Nat.card_zpowers,hz,t.maximal_plane_centralizer_card hc] at hh
    omega
  let P : Sylow 2 C := (IsPGroup.of_card (p:=2) (n:=1) (by rw [Nat.card_zpowers,hz,pow_one])).toSylow
    (by rw [hi]; decide)
  have hgC := (normalizer_le_normalizer_centralizer E) hg
  let v : C := ⟨MulAut.conj g (t.z:G),(hgC (t.z:G)).mp hzC⟩
  have hv : orderOf v=2 := (orderOf_coe v).symm.trans
    (((MulAut.conj g).orderOf_eq (t.z:G)).trans ((orderOf_coe t.z).trans t.z_order))
  obtain ⟨w,hw⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n:=1) hv
  obtain ⟨q,hq⟩ := isConj_iff.mp hw
  have hwz : (w:C)=z := by
    have hm : (w:C)∈zpowers z := w.property
    have hm' : (w:C)=1 ∨ (w:C)=z := by
      rw [mem_zpowers_iff_mem_range_orderOf,hz] at hm
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
      have hi' : i<2 := Finset.mem_range.mp hi
      rw [←he]
      interval_cases i <;> simp
    apply hm'.resolve_left
    intro he
    have hh := (MulAut.conj q).orderOf_eq v
    rw [show MulAut.conj q v=(w:C) from hq,he,orderOf_one,hv] at hh
    omega
  refine ⟨q,q.property,?_⟩
  rw [t.centralizer]
  apply mem_centralizer_singleton_iff.mpr
  have he : (q:G)*(g*(t.z:G)*g⁻¹)*(q:G)⁻¹=(t.z:G) :=
    congrArg Subtype.val (hq.trans hwz)
  have he' : ((q:G)*g)*(t.z:G)*((q:G)*g)⁻¹=(t.z:G) := by
    simpa only [mul_inv_rev,mul_assoc] using he
  exact mul_inv_eq_iff_eq_mul.mp he'

/-- Every element of the full plane normalizer acts as one common scalar. -/
theorem maximal_plane_normalizer_action (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243)
    (g : G) (hg : g∈normalizer ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G)) :
    (∀ a∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G), MulAut.conj g a=a) ∨
    (∀ a∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G), MulAut.conj g a=a⁻¹) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  obtain ⟨q,hq,hqg⟩ := t.maximal_plane_normalizer_adjust hc g hg
  have hqgN := (normalizer (E:Set G)).mul_mem (Subgroup.centralizer_le_normalizer (E:Set G) hq) hg
  have he (a : G) (ha : a∈E) : MulAut.conj (q*g) a=MulAut.conj g a := by
    have hb : MulAut.conj g a∈E := (hg a).mp ha
    have hcomm := (hq _ hb).symm
    change q*(g*a*g⁻¹)=(g*a*g⁻¹)*q at hcomm
    change (q*g)*a*(q*g)⁻¹=g*a*g⁻¹
    calc
      _ = q*(g*a*g⁻¹)*q⁻¹ := by group
      _ = _ := by rw [hcomm,mul_inv_cancel_right]
  rcases t.local_plane_scalar (q*g) hqg hqgN with h|h
  · exact Or.inl (fun a ha => (he a ha).symm.trans (h a ha))
  · exact Or.inr (fun a ha => (he a ha).symm.trans (h a ha))

/-- The full normalizer splits over the original Klein four, with the literal
three-core of the plane centralizer as its normal subgroup. -/
theorem maximal_plane_normalizer_split (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
    normalizer (E:Set G)=U⊔t.torus.map c.H.subtype ∧
      Disjoint U (t.torus.map c.H.subtype) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
  let A := t.torus.map c.H.subtype
  let C := Subgroup.centralizer (E:Set G)
  let N := normalizer (E:Set G)
  obtain ⟨hu,hUc,hC⟩ := t.maximal_plane_elementary_extension hc
  change C=U⊔zpowers (t.z:G) at hC
  have hAN : A≤N := t.torus_normalizes_plane_subgroup E le_rfl
  have hCN : C≤N := Subgroup.centralizer_le_normalizer _
  have hzA : zpowers (t.z:G)≤A := zpowers_le.mpr
    (mem_map_of_mem c.H.subtype (mem_sup_left (mem_zpowers _)))
  have hCA : C≤U⊔A := by rw [hC]; exact sup_le_sup_left hzA U
  have hnA : (t.n:G)∈A := mem_map_of_mem c.H.subtype (mem_sup_right (mem_zpowers _))
  have hNC : N≤C⊔zpowers (t.n:G) := by
    intro g hg
    rcases t.maximal_plane_normalizer_action hc g hg with h|h
    · exact mem_sup_left (fun a ha => (mul_inv_eq_iff_eq_mul.mp (h a ha)).symm)
    · have hgn : g*(t.n:G)⁻¹∈C := by
        intro a ha
        have hni : (MulAut.conj (t.n:G))⁻¹ a=a⁻¹ := by
          apply (MulAut.conj (t.n:G)).injective
          simp only [MulAut.inv_apply,MulEquiv.apply_symm_apply,map_inv,t.plane_inverted a ha,inv_inv]
        have he : MulAut.conj (g*(t.n:G)⁻¹) a=a := by
          change (g*(t.n:G)⁻¹)*a*(g*(t.n:G)⁻¹)⁻¹=a
          calc
            _ = g*((t.n:G)⁻¹*a*(t.n:G))*g⁻¹ := by group
            _ = MulAut.conj g a⁻¹ := by rw [show (t.n:G)⁻¹*a*(t.n:G)=a⁻¹ from hni]; rfl
            _ = a := by rw [map_inv,h a ha,inv_inv]
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      have hh := (C⊔zpowers (t.n:G)).mul_mem (mem_sup_left hgn) (mem_sup_right (mem_zpowers _))
      simpa only [inv_mul_cancel_right] using hh
  refine ⟨le_antisymm (hNC.trans (sup_le hCA ((zpowers_le.mpr hnA).trans le_sup_right)))
    (sup_le ((show U≤C by rw [hC]; exact le_sup_left).trans hCN) hAN),?_⟩
  let : IsKleinFour A := t.ambient_torus_kleinFour
  exact disjoint_of_coprime_natCard (by rw [hUc,IsKleinFour.card_four]; decide)

/-- The full plane normalizer preserves the actual elementary81. -/
theorem maximal_plane_extension_normalized (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
    normalizer (E:Set G) ≤ normalizer (U:Set G) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let C := Subgroup.centralizer (E:Set G)
  dsimp only
  have he := t.maximal_plane_threeCore hc
  have hh := (normalizer_le_normalizer_centralizer E).trans
    (normalizer_le_normalizer_characteristic_image C (pCore 3 C))
  change normalizer (E:Set G) ≤ normalizer (C.pCoreIn 3:Set G) at hh
  rw [he] at hh
  exact hh

/-- The full normalizer has order324, with no uncomputed automorphism factor. -/
theorem maximal_plane_normalizer_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (normalizer
      ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G))=324 := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
  let A := t.torus.map c.H.subtype
  have hAN : A≤normalizer (U:Set G) :=
    (t.torus_normalizes_plane_subgroup E le_rfl).trans (t.maximal_plane_extension_normalized hc)
  let : IsKleinFour A := t.ambient_torus_kleinFour
  obtain ⟨he,hd⟩ := t.maximal_plane_normalizer_split hc
  rw [he,card_sup_eq_mul_of_normalizes_of_disjoint U A hAN hd,
    (t.maximal_plane_elementary_extension hc).2.1,IsKleinFour.card_four]

/-- The elementary81 is also the three-core of the full plane normalizer. -/
theorem maximal_plane_normalizer_threeCore (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
    (normalizer (E:Set G)).pCoreIn 3=U := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
  let N := normalizer (E:Set G)
  obtain ⟨hu,hUc,_⟩ := t.maximal_plane_elementary_extension hc
  let : IsElementaryAbelian 3 U := hu
  have hUN : U≤N := by
    have he := (t.maximal_plane_normalizer_split hc).1
    change N=U⊔_ at he
    rw [he]
    exact le_sup_left
  have hle : U≤N.pCoreIn 3 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 3 U) hUN (t.maximal_plane_extension_normalized hc)
  have ho : Nat.Coprime (Nat.card (N.pCoreIn 3)) 4 := by
    obtain ⟨i,hi⟩ := (isPGroup_pCoreIn 3 N).exists_card_eq
    rw [hi]
    exact (by decide : Nat.Coprime 3 4).pow_left i
  have hd : Nat.card (N.pCoreIn 3)∣81 := by
    have hh := card_dvd_of_le (pCoreIn_le 3 N)
    rw [t.maximal_plane_normalizer_card hc] at hh
    exact ho.dvd_of_dvd_mul_left hh
  exact (eq_of_le_of_card_ge hle (by rw [hUc]; exact Nat.le_of_dvd (by decide) hd)).symm

/-- The original plane is exactly the fixed subgroup of its central involution
on the canonical elementary81. -/
theorem maximal_plane_extension_inf_H (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    (E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y))⊓c.H=E := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
  have hE : Nat.card E=9 := (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hEH : E≤c.H := sup_le (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property)
  have hdU : Nat.card (U⊓c.H:Subgroup G)∣81 := by
    have hh := card_dvd_of_le (show U⊓c.H≤U from inf_le_left)
    rw [(t.maximal_plane_elementary_extension hc).2.1] at hh
    exact hh
  have hdH : Nat.card (U⊓c.H:Subgroup G)∣576 := by
    have hh := card_dvd_of_le (show U⊓c.H≤c.H from inf_le_right)
    rwa [H_card c] at hh
  have hd : Nat.card (U⊓c.H:Subgroup G)∣9 := Nat.dvd_gcd hdU hdH
  exact (eq_of_le_of_card_ge (le_inf le_sup_left hEH)
    (by rw [hE]; exact Nat.le_of_dvd (by decide) hd)).symm

/-- The centralizer of the marked involution inside the full elementary81
normalizer is the original plane times the original Klein four. -/
theorem maximal_extension_normalizer_inf_H (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
    normalizer (U:Set G)⊓c.H=E⊔t.torus.map c.H.subtype := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
  let A := t.torus.map c.H.subtype
  have hAH : A≤c.H := map_subtype_le _
  have hAN : A≤normalizer (U:Set G) :=
    (t.torus_normalizes_plane_subgroup E le_rfl).trans (t.maximal_plane_extension_normalized hc)
  have hEH : E≤c.H := sup_le (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property)
  have hEN : E≤normalizer (U:Set G) := (show E≤U from le_sup_left).trans U.le_normalizer
  apply le_antisymm ?_ (sup_le (le_inf hEN hEH) (le_inf hAN hAH))
  intro g hg
  have hgN : g∈normalizer (E:Set G) := by
    have hfixed : U⊓c.H=E := t.maximal_plane_extension_inf_H hc
    rw [←hfixed]
    exact inf_normalizer_le_normalizer_inf ⟨hg.1,c.H.le_normalizer hg.2⟩
  have he := (t.maximal_plane_normalizer_split hc).1
  change normalizer (E:Set G)=U⊔A at he
  have hg' : g∈(U:Set G)*(A:Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U A hAN,←he]
    exact hgN
  obtain ⟨u,hu,a,ha,hua⟩ := hg'
  have huH : u∈c.H := by
    have hh := c.H.mul_mem hg.2 (c.H.inv_mem (hAH ha))
    simpa only [←hua,mul_inv_cancel_right] using hh
  have hfixed : U⊓c.H=E := t.maximal_plane_extension_inf_H hc
  have huE : u∈E := hfixed ▸ (show u∈U⊓c.H from ⟨hu,huH⟩)
  exact hua ▸ mul_mem_sup huE ha

/-- This centralizer has order36 in the full elementary81 normalizer. -/
theorem maximal_extension_normalizer_involution_centralizer_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
    Nat.card (normalizer (U:Set G)⊓Subgroup.centralizer ({(t.z:G)}:Set G):Subgroup G)=36 := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let A := t.torus.map c.H.subtype
  have hE : Nat.card E=9 := (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  let : IsKleinFour A := t.ambient_torus_kleinFour
  have hd : Disjoint E A := disjoint_of_coprime_natCard (by rw [hE,IsKleinFour.card_four]; decide)
  dsimp only
  rw [←t.centralizer,t.maximal_extension_normalizer_inf_H hc,
    card_sup_eq_mul_of_normalizes_of_disjoint E A (t.torus_normalizes_plane_subgroup E le_rfl) hd,
    hE,IsKleinFour.card_four]

/-- In the faithful quotient N(U)/C(U), where C(U)=U, the marked central
involution has centralizer isomorphic to the original Klein four torus. -/
theorem maximal_extension_quotient_involution_centralizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
    let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
    ∃ z : normalizer (U:Set G), (z:G)=(t.z:G) ∧
      orderOf (NormalizerAction.quotient U z)=2 ∧
      Nonempty ((Subgroup.centralizer
        ({NormalizerAction.quotient U z}:Set (NormalizerAction.Star U))) ≃*
          t.torus.map c.H.subtype) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
  let N := normalizer (U:Set G)
  let A := t.torus.map c.H.subtype
  let q := NormalizerAction.quotient U
  have hAN : A≤N := (t.torus_normalizes_plane_subgroup E le_rfl).trans
    (t.maximal_plane_extension_normalized hc)
  have hEN : E≤N := (show E≤U from le_sup_left).trans U.le_normalizer
  have hCU : Subgroup.centralizer (U:Set G)=U := t.maximal_plane_extension_selfCentralizing hc
  have hUcard : Nat.card U=81 := (t.maximal_plane_elementary_extension hc).2.1
  have hkernel : NormalizerAction.C U=U.subgroupOf N := by rw [NormalizerAction.C,hCU]
  have hkernelcard : Nat.card (NormalizerAction.C U)=81 := by
    rw [hkernel,Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv,hUcard]
  have hzA : (t.z:G)∈A := mem_map_of_mem c.H.subtype (mem_sup_left (mem_zpowers _))
  let z : N := ⟨t.z,hAN hzA⟩
  have hz : orderOf z=2 := (orderOf_coe z).symm.trans ((orderOf_coe t.z).trans t.z_order)
  have hqz : orderOf (q z)=2 := by
    apply orderOf_eq_prime
    · rw [←map_pow,show z^2=1 from hz ▸ pow_orderOf_eq_one z,map_one]
    · intro he
      have hzU : (t.z:G)∈U := hCU ▸ ((NormalizerAction.quotient_eq_one_iff U z).mp he)
      have hh := U.orderOf_dvd_natCard hzU
      rw [orderOf_coe,t.z_order,hUcard] at hh
      norm_num at hh
  have hzC : Subgroup.centralizer ({z}:Set N)=(E⊔A).subgroupOf N := by
    apply (map_injective N.subtype_injective)
    rw [map_subtype_centralizer_singleton,map_subgroupOf_eq_of_le (sup_le hEN hAN)]
    change N⊓Subgroup.centralizer ({(t.z:G)}:Set G)=E⊔A
    rw [←t.centralizer]
    exact t.maximal_extension_normalizer_inf_H hc
  have hmap : Subgroup.centralizer ({q z}:Set (NormalizerAction.Star U))=
      (A.subgroupOf N).map q := by
    let : Fact (IsPGroup 2 (zpowers z)) := ⟨IsPGroup.of_card (p:=2) (n:=1)
      (by rw [Nat.card_zpowers,hz,pow_one])⟩
    have hlift := centralizer_map_quotient_eq_map_centralizer 2 (zpowers z)
      (NormalizerAction.C U) inferInstance (by rw [hkernelcard]; decide)
    change Subgroup.centralizer ((zpowers z).map q : Set (NormalizerAction.Star U))=
      (Subgroup.centralizer (zpowers z:Set N)).map q at hlift
    rw [MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure,
      zpowers_eq_closure,centralizer_closure,hzC,
      subgroupOf_sup hEN hAN,Subgroup.map_sup] at hlift
    have he : (E.subgroupOf N).map q=⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
      intro a ha
      exact (NormalizerAction.quotient_eq_one_iff U a).mpr
        (hCU.symm ▸ (show (a:G)∈U from mem_sup_left ha)))
    simpa only [he,bot_sup_eq] using hlift
  let f : A →* NormalizerAction.Star U := q.comp (inclusion hAN)
  have hfi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (by
    apply bot_unique
    intro a ha
    have haU : (a:G)∈U := hCU ▸ ((NormalizerAction.quotient_eq_one_iff U (inclusion hAN a)).mp ha)
    exact Subtype.ext ((t.maximal_plane_normalizer_split hc).2.le_bot ⟨haU,a.property⟩))
  have hr : f.range=Subgroup.centralizer ({q z}:Set (NormalizerAction.Star U)) := by
    rw [hmap,MonoidHom.range_comp]
    congr 1
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a,ha⟩,rfl⟩
  exact ⟨z,rfl,hqz,⟨((MonoidHom.ofInjective hfi).trans (MulEquiv.subgroupCongr hr)).symm⟩⟩

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
