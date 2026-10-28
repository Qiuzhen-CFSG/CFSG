module

public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.OddCore
public import Theory.SpecificGroups.Suzuki.SylowSquares

/-!
# Borel placement for a prescribed embedded Suzuki Sylow subgroup

Every nonidentity square in the standard symplectic unipotent group U has
both central-root coordinates nonzero, and hence has full centralizer U.
If a subgroup of U contains such a square, its normalizer preserves U and
lies in the original Borel. A Suzuki Sylow has nonidentity squares, so
this applies to any prescribed Suzuki Sylow lying in U, independently of
the abstract embedding and without a natural-module recognition premise.

Source: Aschbacher--Smith E.2.7, printed pp.220--221, the original Borel
marking for the Suzuki branch. The square formula also covers the smallest
ambient field of order two; the Suzuki specialization has parameter m≥1.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
open TwoConjugate CentralRootGeometry
open BenderSuzuki.MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every nonidentity square in the original unipotent subgroup has that
whole subgroup as its ambient centralizer. -/
theorem centralizer_square_eq_unipotent
    (x : unipotent (F := F)) (hx : x^2≠1) :
    centralizer ({((x : Sp F)^2)} : Set (Sp F)) = unipotent := by
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hb : b≠0 := by
    intro h
    apply hx
    simp only [element_square,h,zero_pow (by decide : 2≠0),zero_mul,theta]
    exact element_zero
  have hv : v≠0 := by
    intro h
    apply hx
    simp only [element_square,h,mul_zero,theta]
    exact element_zero
  have he : ((element b u w v : unipotent (F := F)) : Sp F)^2 =
      upper (b^2*v) (b*v) := by
    rw [← Subgroup.coe_pow,element_square,theta_val]
    rfl
  rw [he]
  exact centralizer_upper_eq_unipotent _ _
    (mul_ne_zero (pow_ne_zero 2 hb) hv) (mul_ne_zero hb hv)

/-- An order-four element in a subgroup of U determines the original Borel
for its entire ambient normalizer. -/
theorem normalizer_le_borel_of_nontrivial_square
    (S : Subgroup (Sp F)) (hSU : S≤unipotent)
    (hsq : ∃x : S, x^2≠1) : normalizer (S : Set (Sp F))≤borel := by
  obtain ⟨x,hx⟩ := hsq
  let u : unipotent (F := F) := ⟨x,hSU x.property⟩
  have hu : u^2≠1 := by
    intro h
    apply hx
    apply Subtype.ext
    exact congrArg (fun z : unipotent (F := F) => (z : Sp F)) h
  intro g hg
  let a := MulAut.conj g
  have hyS : a (x : Sp F)∈S := (mem_normalizer_iff.mp hg _).mp x.property
  let y : unipotent (F := F) := ⟨a x,hSU hyS⟩
  have hy : y^2≠1 := by
    intro h
    have he : a ((x : Sp F)^2)=1 := by
      have hh := congrArg (fun z : unipotent (F := F) => (z : Sp F)) h
      change (a (x : Sp F))^2=1 at hh
      simpa only [map_pow] using hh
    exact hx (Subtype.ext (a.map_eq_one_iff.mp he))
  have hC := centralizer_square_eq_unipotent u hu
  have hD := centralizer_square_eq_unipotent y hy
  rw [borel_eq_normalizer_unipotent,mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨z,hz,rfl⟩
    rw [←hD,mem_centralizer_singleton_iff]
    have hc := mem_centralizer_singleton_iff.mp (hC.symm ▸ hz)
    change a z * (a (x : Sp F))^2 = (a (x : Sp F))^2 * a z
    simpa only [map_mul,map_pow] using congrArg a hc
  · rw [card_map_of_injective a.injective]

/-- The normalizer of any prescribed embedded Suzuki Sylow lying in U
lies in the original symplectic Borel. -/
theorem suzuki_sylow_normalizer_le_borel
    (P : Subgroup (Sp F)) {m : ℕ} (hm : 0<m)
    (e : P ≃* SuzukiMatrixGroup m) (S : Sylow 2 P)
    (hSU : (S : Subgroup P)≤(unipotent (F := F)).subgroupOf P) :
    normalizer (S : Set P)≤(borel (F := F)).subgroupOf P := by
  let A := (S : Subgroup P).map P.subtype
  have hAU : A≤unipotent := by
    rintro _ ⟨x,hx,rfl⟩
    exact hSU hx
  obtain ⟨x,hx⟩ := suzukiSylow_exists_nontrivial_square hm e S
  have hsq : ∃x : A,x^2≠1 := by
    refine ⟨⟨x.val.val,mem_map_of_mem P.subtype x.property⟩,?_⟩
    intro h
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z : Sp F)) h
  have hn := normalizer_le_borel_of_nontrivial_square A hAU hsq
  intro g hg
  apply hn
  exact (S : Subgroup P).le_normalizer_map P.subtype
    (mem_map_of_mem P.subtype hg)

end Theory.SpecificGroups.SymplecticFour
