module
public import Theory.GroupTheory.Commutator.PrimeImage
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# A cubic residual joined to a moving two-subgroup

Let a two-group R normalize a two-perfect subgroup Y. Suppose Y has an
order-three image, its action kernel is a two-group contained in R, and R
moves that image. Then Y=[Y,R], and R is Sylow of index three in YR.
Its nonnormality identifies YR/O₂(YR) with the actual symmetric group S₃.
Only the kernel on Y must be a two-group; the whole action kernel is unrestricted.

Source application: Aschbacher--Smith 15.2.6, printed p.1109, the marked
cubic and cyclic Omega selections, with the literal intersection core Rc.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- A moving cubic image supplies full movement and the intrinsic S₃ quotient. -/
theorem cubic_join_of_moving_prime_image
    (Y R : Subgroup G) (f : G →* D)
    (hY : IsPPerfect 2 Y) (hR : IsPGroup 2 R)
    (hn : R ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y.map f) = 3)
    (hk : IsPGroup 2 (Y ⊓ f.ker : Subgroup G))
    (hkr : Y ⊓ f.ker ≤ R)
    (hm : ¬ R.map f ≤ centralizer (Y.map f : Set D)) :
    ⁅Y,R⁆ = Y ∧ Y ≠ ⊥ ∧
      Nonempty (((Y ⊔ R : Subgroup G) ⧸ pCore 2 (Y ⊔ R : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) := by
  have hnot : ¬ Y ≤ normalizer (R : Set G) := by
    intro hy
    have hdis : Disjoint (Y.map f) (R.map f) :=
      IsPGroup.disjoint_of_coprime
        (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hc))
        (hR.map f) (by decide : Nat.Coprime 3 2)
    have hbot : ⁅Y.map f,R.map f⁆ = ⊥ := by
      rw [←map_commutator]
      apply bot_unique
      exact (le_inf (map_mono (le_normalizer_iff_commutator_le_left.mp hn))
        (map_mono (le_normalizer_iff_commutator_le_right.mp hy))).trans hdis.le_bot
    exact hm (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot))
  have hmovement : ⁅Y,R⁆ = Y := by
    rcases eq_commutator_or_normalizes_of_prime_image Y R f hY hn hk hkr
      (by rw [hc]; decide) with he | he
    · exact he.symm
    · exact (hnot he).elim
  have hne : Y ≠ ⊥ := by
    intro he
    rw [he,map_bot,card_bot] at hc
    omega
  let a := f.comp Y.subtype
  have ha : a.range = Y.map f := by rw [MonoidHom.range_comp,range_subtype]
  have hak : IsPGroup 2 a.ker := by
    have he : a.ker = (Y ⊓ f.ker).subgroupOf Y := by
      ext y
      exact (and_iff_right y.property).symm
    rw [he]
    exact hk.comap_subtype
  have hi : a.ker.index = 3 := by rw [index_ker,ha]; exact hc
  let P : Sylow 2 Y := hak.toSylow (by rw [hi]; decide)
  have hcore : pCore 2 Y = a.ker := le_antisymm
    (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨inferInstance,hak⟩)
  have hcoreR : Y.pCoreIn 2 ≤ R := by
    change (pCore 2 Y).map Y.subtype ≤ R
    rw [hcore]
    rintro x ⟨y,hy,rfl⟩
    exact hkr ⟨y.property,hy⟩
  obtain ⟨S,hS⟩ := hR.exists_sylow_sup_of_coprime_index Y R hn (pCore 2 Y)
    (by rw [hcore,hi]; decide) hcoreR
  let L := Y ⊔ R
  have hSR : (S : Subgroup L) = R.subgroupOf L := by
    have hh := congrArg (comap L.subtype) hS
    rwa [comap_map_eq_self_of_injective L.subtype_injective] at hh
  let P₀ : Sylow 2 Y := pCore_isPGroup.toSylow (by rw [hcore,hi]; decide)
  have hRY : R.subgroupOf Y = pCore 2 Y :=
    P₀.is_maximal' hR.comap_subtype
      (fun y hy => hcoreR (mem_map_of_mem Y.subtype hy))
  have hindex : (S : Subgroup L).index = 3 := by
    rw [hSR]
    change R.relIndex (Y ⊔ R) = 3
    rw [relIndex_sup_of_normalizes_left Y R hn]
    change (R.subgroupOf Y).index = 3
    rwa [hRY,hcore]
  refine ⟨hmovement,hne,sylow_index_three_core_quotient S hindex ?_⟩
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
  intro he
  have hRN : (R.subgroupOf L).Normal := by rw [←hSR,←he]; infer_instance
  exact hnot (le_sup_left.trans
    ((normal_subgroupOf_iff_le_normalizer (show R ≤ L from le_sup_right)).mp hRN))

end Subgroup
