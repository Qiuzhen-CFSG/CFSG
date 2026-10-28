module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoCartanRows
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanPermutability

/-!
# The original tensor Cartan factor orbits

Hall conjugacy in N_{L₀}(T ∩ L₀) factors T through T ∩ L₀ and N_T(A).
Since L₀ normalizes L, the latter contains an element exchanging the two
original component factors. The marked A₅-pair quotient is injective on A;
its two cubic axes are disjoint and generate A. Each axis therefore has
literal N_T(A)-orbit A. The final theorem applies this to the original
Omega action quotient and excludes both linear-three action rows.

Source: Aschbacher--Smith 9.3.8--9, printed p.734, using the Cartan
and A₅-pair geometry of 9.2.7 and 9.3.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterC.MSCentralOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include m in
theorem exists_moving_cartan_normalizer (A : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hAe : IsElementaryAbelian 3 A) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (L : Set G) ∧
      t ∈ normalizer (A : Set G) := by
  let R := localOrbit T L
  let U := (T : Subgroup G) ⊓ R
  let N := sourceOrbitSylowNormalizer T L
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := le_normalizer_componentOrbit L T
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTR).trans inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf hTR (hTU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hAU : A ≤ normalizer (U : Set G) := hAB.trans ((map_subtype_le _).trans inf_le_right)
  have hN : N = U ⊔ A := m.cartan_orbit_sylow_normalizer_eq_sup A hAB hA9
  have hUN : U ≤ N := hN ▸ le_sup_left
  have hAN : A ≤ N := hN ▸ le_sup_right
  have hpU : IsPGroup 2 U := (T.isPGroup').to_le inf_le_left
  let : Group.IsNilpotent U := hpU.isNilpotent
  let := hAe
  have hsol : Group.IsSolvable N := by
    rw [hN]
    exact Group.isSolvable_sup_of_normalizes U A hAU
  have hHall := OddHall.oddHall_of_normalized_sup hpU
    (show Nat.Coprime 2 (Nat.card A) by rw [hA9]; decide) hAU hN.symm
  have hodd : ¬ 2 ∣ (U.subgroupOf N).index := by
    change ¬ 2 ∣ U.relIndex N
    rw [hN,OddHall.relIndex_normalized_sup U A hAU]
    intro hd
    have hh := hd.trans (relIndex_dvd_card U A)
    rw [hA9] at hh
    norm_num at hh
  let P := hpU.comap_subtype.toSylow hodd
  have hP : (P : Subgroup N).map N.subtype = U := map_subgroupOf_eq_of_le hUN
  have hfrat := OddHall.normal_sylow_frattini N U T A hsol inf_le_left hTN P hP hAN hHall
  obtain ⟨s,hs,hsn⟩ := SetLike.not_le_iff_exists.mp m.sylow_not_normalizes_component
  have hs' : s ∈ (U : Set G) * ((T ⊓ normalizer (A : Set G) : Subgroup G) : Set G) := hfrat ▸ hs
  obtain ⟨u,hu,t,ht,he⟩ := hs'
  refine ⟨t,ht.1,?_,ht.2⟩
  intro htn
  exact hsn (he ▸ (normalizer (L : Set G)).mul_mem
    (source_nonnormal_orbit_le_normalizer D m.sylow_not_normalizes_component hu.2) htn)

include m in
private theorem cartan_cubic_conjugate_sup (A C : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hAe : IsElementaryAbelian 3 A) (hCA : C ≤ A) (hCL : C ≤ L)
    (hC3 : Nat.card C = 3) {t : G} (ht : t ∈ (T : Subgroup G))
    (htn : t ∉ normalizer (L : Set G)) (htA : t ∈ normalizer (A : Set G)) :
    C ⊔ C.map (MulAut.conj t).toMonoidHom = A := by
  let R := localOrbit T L
  have hAR : A ≤ R := hAB.trans ((map_subtype_le _).trans inf_le_left)
  let q := originalA5ProductProjection D e m.sylow_not_normalizes_component ht htn
  have hk : IsPGroup 2 q.ker := by rw [originalA5ProductProjection_ker]; exact pCore_isPGroup
  let r := q.comp (inclusion hAR)
  have hr : Function.Injective r := source_a5_borel_torus_quotient_injective A hAB
    (IsPGroup.of_card (n := 2) hA9) q hk
  let C' := C.map (MulAut.conj t).toMonoidHom
  have hC'A : C' ≤ A := (map_mono hCA).trans_eq (mem_normalizer_iff_map_conj_eq.mp htA)
  have hd : Disjoint C C' := by
    apply disjoint_def.mpr
    intro x hx hx'
    obtain ⟨y,hy,he⟩ := mem_map.mp hx'
    have hfirst : q ⟨x,hAR (hCA hx)⟩ = (e (QuotientGroup.mk' _ ⟨x,hCL hx⟩),1) :=
      originalA5ProductProjection_first D e m.sylow_not_normalizes_component ht htn ⟨x,hCL hx⟩
    have hsecond : q ⟨x,hAR (hCA hx)⟩ = (1,e (QuotientGroup.mk' _ ⟨y,hCL hy⟩)) := by
      have he' : (⟨x,hAR (hCA hx)⟩ : R) = originalConjugateOrbitInclusion ht ⟨y,hCL hy⟩ :=
        Subtype.ext he.symm
      rw [he']
      exact originalA5ProductProjection_second D e m.sylow_not_normalizes_component ht htn _
    have hone : r ⟨x,hCA hx⟩ = 1 := by
      change q ⟨x,hAR (hCA hx)⟩ = 1
      rw [hfirst]
      have hf := congrArg (fun p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) => p.1)
        (hfirst.symm.trans hsecond)
      exact Prod.ext hf rfl
    exact congrArg Subtype.val (hr (hone.trans r.map_one.symm))
  let := hAe
  have hn : C' ≤ normalizer (C : Set G) :=
    (hC'A.trans ((le_centralizer A).trans (centralizer_le hCA))).trans (Subgroup.centralizer_le_normalizer _)
  apply eq_of_le_of_card_ge (sup_le hCA hC'A)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint C C' hn hd,
    show Nat.card C' = Nat.card C from card_map_of_injective (MulAut.conj t).injective,hC3,hA9]

namespace GenerationTwoOvergroup
variable {m} (c : m.GenerationTwoOvergroup)

/-- Each original Cartan factor generates the full Cartan under its literal Sylow normalizer. -/
theorem cartanOrbits : c.CartanOrbits := by
  obtain ⟨t,ht,htn,htA⟩ := m.exists_moving_cartan_normalizer c.A c.borel c.card_cartan c.elementary_cartan
  obtain ⟨C,hCA,hCL,hC3⟩ := m.old_residual_cartan_component_cubic c.A c.borel c.card_cartan
  have hgen := m.cartan_cubic_conjugate_sup c.A C c.borel c.card_cartan c.elementary_cartan
    hCA hCL hC3 ht htn htA
  let S := (T : Subgroup G) ⊓ normalizer (c.A : Set G)
  let C' := C.map (MulAut.conj t).toMonoidHom
  have htS : t ∈ S := ⟨ht,htA⟩
  have hC'A : C' ≤ c.A := (map_mono hCA).trans_eq (mem_normalizer_iff_map_conj_eq.mp htA)
  have hC'L : C' ≤ L.map (MulAut.conj t).toMonoidHom := map_mono hCL
  have hfirst : componentOrbit (c.A ⊓ L) S = c.A := by
    apply le_antisymm (iSup_conjugates_le_of_le_normalizer (c.A ⊓ L) S c.A inf_le_left inf_le_right)
    apply hgen.ge.trans
    apply sup_le ((le_inf hCA hCL).trans (le_componentOrbit (c.A ⊓ L) S))
    exact (map_mono (le_inf hCA hCL)).trans
      (le_iSup (fun s : S => (c.A ⊓ L).map (MulAut.conj (s : G)).toMonoidHom) ⟨t,htS⟩)
  refine ⟨hfirst,t,ht,htn,?_⟩
  apply le_antisymm (iSup_conjugates_le_of_le_normalizer
    (c.A ⊓ L.map (MulAut.conj t).toMonoidHom) S c.A inf_le_left inf_le_right)
  have hC' : C' ≤ componentOrbit (c.A ⊓ L.map (MulAut.conj t).toMonoidHom) S :=
    (le_inf hC'A hC'L).trans (le_componentOrbit _ _)
  have hC : C ≤ componentOrbit (c.A ⊓ L.map (MulAut.conj t).toMonoidHom) S := by
    have hh := (map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hC').trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit _ S (S.inv_mem htS)))
    have he : C'.map (MulAut.conj t⁻¹).toMonoidHom = C := by
      change (C.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = C
      rw [map_map]
      have hc : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [mul_assoc]
      rw [hc,map_id]
    rwa [he] at hh
  exact hgen.ge.trans (sup_le hC hC')

/-- Both original linear action rows are impossible on the literal Omega quotient. -/
theorem not_linear
    (hr : IsPReduced 2 (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))) :
    letI := hr.normal
    ¬ Nonempty (((pResidual 2 c.M).map (actionMk (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))) ≃*
      SL(3,ChapterB.QuasisimpleSource.BinaryField.four.Carrier)) :=
  c.not_linear_of_cartanOrbits c.cartanOrbits hr

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
