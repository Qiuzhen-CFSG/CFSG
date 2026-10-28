module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOmegaFour
public import Stellmacher.OmegaCenterCentralizer

/-!
# The left fixed spaces and Cartan intersection in the A₇ configuration

In the faithful binary four-space, the Sylow fixed-line stabilizer is maximal
and has order 168. The actual right Hall plane has order nine, so it escapes
that stabilizer. Lifting through the literal two-core proves that this Hall
plane and the original omega-centralizer generate the whole right local join.
Both Hall factors normalize L, so the omega-centralizer must escape N_G(L).
Uniqueness over LT then kills every left-fixed central involution. The finite
two-group center principle eliminates the full Sylow centralizer, and hence
the fixed spaces on the arbitrary original W and its commutator layer.

The cyclic odd Cartan injects into the actual A₇ quotient on its intersection
with the maximal component. The seven-letter order restriction identifies
that intersection with the original escaping cubic. The existing natural
fixed-space comparison then gives the cubic fixed-space vanishings as well.
The final application discharges the A₇-configuration premise using the
completed FF reduction, preserving the universal Sylow/module contract.

These are the fixed-space and intersection steps of 5.1.13. The two block
exclusions and torus argument remain necessary for centralization.
Source: Aschbacher–Smith 5.1.13, printed pp.637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

/-- The actual Hall plane and omega-centralizer generate the whole right join. -/
theorem LocalA7Configuration.four_hall_omega_generation
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    B ⊔ D ⊔ ((K ⊔ (T : Subgroup G)) ⊓ omegaCentralizer T) =
      K ⊔ (T : Subgroup G) := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  have hc := a.four h hH hgen c d
  obtain ⟨q,hq,hk,hcore⟩ := a.four_action h hc
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hf := NormalElementaryQuotient.representation_injective U q hq hk
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = Nat.card (ZMod 2)^Module.finrank (ZMod 2) (Additive U) at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv,hc,Nat.card_zmod] at hh
    exact hh.symm
  let C := subspaceKernel ρ (fixedSpace ρ ((P : Subgroup M).map q)) ⊤
  have hcoat : IsCoatom C :=
    Representation.BinaryAlternatingSevenControl.sylow_fixedKernel_coatom ρ hf hd (P.mapSurjective hq)
  have hCc : Nat.card C = 168 := by
    have hi := Representation.BinaryAlternatingSevenControl.sylow_fixedKernel_index ρ hf hd (P.mapSurjective hq)
    change C.index = 15 at hi
    have hh := C.card_mul_index
    rw [hi,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hZ := (a.omega_four_geometry h hH hgen c d).1
  have hCZ : (C.comap q).map M.subtype ≤ omegaCentralizer T := by
    rintro _ ⟨g,hg,rfl⟩ z hz
    let v : Additive U := Additive.ofMul ⟨⟨z,a.reduced.1 (hZ hz)⟩,hZ hz⟩
    have hv : v ∈ fixedSpace ρ ((P : Subgroup M).map q) := by
      apply (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk (P : Subgroup M) v).mpr
      intro t ht
      apply Subtype.ext
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t.val ht
    have he := hg.2 v hv
    change NormalElementaryQuotient.representation U q hq hk (q g) v = v at he
    have he' := congrArg (fun w : Additive U => (w.toMul : M)) he
    rw [NormalElementaryQuotient.representation_apply] at he'
    have he'' := congrArg M.subtype he'
    change (g : G) * z * (g : G)⁻¹ = z at he''
    exact (mul_inv_eq_iff_eq_mul.mp he'').symm
  let N := (B ⊔ D ⊔ (M ⊓ omegaCentralizer T)).subgroupOf M
  have hker : q.ker ≤ N := by
    intro x hx
    have hxT : (x : G) ∈ (T : Subgroup G) :=
      (hcore.symm ▸ pCore_isPGroup.le_sylow_of_normal P) hx
    exact (show M ⊓ omegaCentralizer T ≤ B ⊔ D ⊔ (M ⊓ omegaCentralizer T) from le_sup_right)
      ⟨x.property,sylow_le_omegaCentralizer hxT⟩
  have hCN' : C ≤ N.map q := by
    rw [←map_comap_eq_self_of_surjective hq C]
    apply map_mono
    intro g hg
    exact (show M ⊓ omegaCentralizer T ≤ B ⊔ D ⊔ (M ⊓ omegaCentralizer T) from le_sup_right)
      ⟨g.property,hCZ (mem_map_of_mem M.subtype hg)⟩
  obtain ⟨_,hEc,hEX,_⟩ := d.hall_cubic_plane h hH hgen c
  have hEM : B ⊔ D ≤ M := hEX.trans (a.contains.trans le_sup_left)
  let E := (B ⊔ D).subgroupOf M
  have hEc' : Nat.card E = 9 := (Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv).trans hEc
  have hdis : Disjoint E q.ker :=
    (IsPGroup.of_card (p := 3) (n := 2) hEc').disjoint_of_coprime
      (hcore.symm ▸ pCore_isPGroup) (by decide)
  have hqi : Function.Injective (q.subgroupMap E) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp (hdis.le_bot ⟨x.property,congrArg Subtype.val (show q.subgroupMap E x = 1 from hx)⟩)
  have hEq : Nat.card (E.map q) = 9 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap E)
      ⟨hqi,q.subgroupMap_surjective E⟩).toEquiv).symm.trans hEc'
  have hEN : E ≤ N := comap_mono le_sup_left
  have hNt : N.map q = ⊤ := by
    apply hcoat.2
    apply lt_of_le_of_ne hCN'
    intro he
    have hdiv := card_dvd_of_le ((map_mono hEN).trans_eq he.symm)
    rw [hEq,hCc] at hdiv
    norm_num at hdiv
  have hN : N = ⊤ := by
    rw [←comap_map_eq_self hker,hNt,comap_top]
  apply le_antisymm (sup_le hEM inf_le_left)
  intro g hg
  exact (show (⟨g,hg⟩ : M) ∈ N from hN ▸ mem_top _)

/-- The original omega-centralizer escapes the unique maximal local over LT. -/
theorem LocalA7Configuration.omega_centralizer_escape
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    ¬ omegaCentralizer T ≤ normalizer (L : Set G) := by
  intro hCN
  have hEN : B ⊔ D ≤ normalizer (L : Set G) :=
    sup_le (c.right_le.trans inf_le_left)
      (((d.cubic_le.trans inf_le_left).trans c.left_le).trans (inf_le_left.trans L.le_normalizer))
  have hMN : K ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) := by
    rw [←a.four_hall_omega_generation h hH hgen c d]
    exact sup_le hEN (inf_le_right.trans hCN)
  exact residual_not_le T H (normalizer (L : Set G)) hH.1.1.2
    h.sylow_normalizes hH.1.2 ((d.residual_le.trans a.contains).trans (le_sup_left.trans hMN))

/-- Uniqueness excludes every left-fixed central involution. -/
theorem Input.omega_fixed_eq_bot_of_centralizer_escape
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ omegaCentralizer T ≤ normalizer (L : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro z hz
  by_contra hne
  have hz1 : z ≠ 1 := fun he => hne (mem_bot.mpr he)
  have hzT := (mem_omegaOneCenterAmbient_iff _ _).mp hz.1
  have hCC : omegaCentralizer T ≤ centralizer ({z} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hz.1)
  obtain ⟨N,hCN,hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime hzT.2.1 hz1))
  have hLC : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hz.2 l hl)
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzT.2.2 t ht)
  exact hout ((hCC.trans hCN).trans_eq
    (h.unique_local_join N hN ((sup_le hLC hTC).trans hCN)))

/-- The whole Sylow centralizer and both original left module fixed spaces vanish. -/
theorem LocalA7Configuration.left_fixed_eq_bot
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      W ⊓ centralizer (L : Set G) = ⊥ ∧
      layer L W ⊓ centralizer (L : Set G) = ⊥ := by
  have hZ := h.omega_fixed_eq_bot_of_centralizer_escape
    (a.omega_centralizer_escape h hH hgen c d)
  have hT := inf_centralizer_eq_bot_of_omega_center _ _ T.isPGroup' h.sylow_normalizes hZ
  have hW : W ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ h.reduced_le_sylow).trans_eq hT)
  refine ⟨hT,hW,bot_unique ((inf_le_inf_right _ ?_).trans_eq hW)⟩
  exact le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans (reduced_normalizes h.reduced))

/-- The original Cartan meets the maximal A₇ component in exactly its
escaping cubic, before any normalization of that component is asserted. -/
theorem LocalA7Configuration.cartan_intersection_eq_cubic
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X D) :
    A ⊓ K = D := by
  let C := A ⊓ K
  have hDC : D ≤ C := le_inf (d.cubic_le.trans inf_le_left)
    ((d.cubic_le.trans inf_le_right).trans a.contains)
  let E := C.subgroupOf K
  let eC : E ≃* C := subgroupOfEquivOfLe (show C ≤ K from inf_le_right)
  let j : E →* A := (inclusion (show C ≤ A from inf_le_left)).comp eC.toMonoidHom
  have hj : Function.Injective j := (inclusion_injective (show C ≤ A from inf_le_left)).comp eC.injective
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let : IsCyclic E := isCyclic_of_injective j hj
  have ho : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hEo : Odd (Nat.card E) := ho.of_dvd_nat (card_dvd_of_injective j hj)
  obtain ⟨e⟩ := a.quotient
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker = pCore 2 K := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  have hdis : Disjoint E q.ker := by
    obtain ⟨k,hkc⟩ := (show IsPGroup 2 q.ker from hk.symm ▸ pCore_isPGroup).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hkc]
    exact hEo.coprime_two_right.pow_right k
  have hqi : Function.Injective (q.subgroupMap E) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp (hdis.le_bot ⟨x.property,
      congrArg Subtype.val (show q.subgroupMap E x = 1 from hx)⟩)
  have heq : Nat.card (E.map q) = Nat.card E :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap E)
      ⟨hqi,q.subgroupMap_surjective E⟩).toEquiv).symm
  let : IsCyclic (E.map q) := isCyclic_of_surjective (q.subgroupMap E) (q.subgroupMap_surjective E)
  have hthree : 3 ∣ Nat.card (E.map q) := by
    rw [heq,Nat.card_congr eC.toEquiv,←d.cubic_card]
    exact card_dvd_of_le hDC
  have hcard := Representation.BinaryAlternatingSevenControl.Cartan.odd_cyclic_card_three
    (E.map q) (heq.symm ▸ hEo) hthree
  have hCc : Nat.card C = 3 := by
    rwa [heq,Nat.card_congr eC.toEquiv] at hcard
  exact (eq_of_le_of_card_ge hDC (by rw [hCc,d.cubic_card])).symm

/-- The natural cubic fixed-space comparison now has zero fixed kernel on
both the original module and the original omega-center. -/
theorem LocalA7Configuration.cubic_fixed_eq_bot
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    W ⊓ centralizer (D : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (D : Set G) = ⊥ := by
  have hDL := ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_left
  have hn : D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (a.four_cubic_normalizes_thompson h hH hgen c d (a.four h hH hgen c d))
  refine ⟨?_,?_⟩
  · rw [h.cubic_fixed_eq_of_normalizes_thompson (a.left_thompson_moves h) hDL d.cubic_card hn]
    exact (a.left_fixed_eq_bot h hH hgen c d).2.1
  · rw [a.omega_cubic_fixed_eq_left h hH hgen c d]
    exact h.omega_fixed_eq_bot_of_centralizer_escape
      (a.omega_centralizer_escape h hH hgen c d)

/-- The genuine FF reduction supplies the left fixed-space vanishings and
the exact Cartan intersection from the original noncentral source inputs. -/
theorem localCartan_noncentral_left_fixed
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧ A ⊓ K = D ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      W ⊓ centralizer (L : Set G) = ⊥ ∧
      layer L W ⊓ centralizer (L : Set G) = ⊥ ∧
      W ⊓ centralizer (D : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (D : Set G) = ⊥ := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  obtain ⟨ht,hw,hv⟩ := a.left_fixed_eq_bot h hH hgen c d
  exact ⟨K,a,a.cartan_intersection_eq_cubic h c d,ht,hw,hv,a.cubic_fixed_eq_bot h hH hgen c d⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
