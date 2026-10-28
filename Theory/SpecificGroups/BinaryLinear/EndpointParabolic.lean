module
public import Theory.SpecificGroups.BinaryLinear.InvariantParabolicPair
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.SolvableRank
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup

/-!
# The endpoint parabolic and the centralizer of a binary Sylow center

A nonidentity central Sylow element is a transvection. Its centralizer fixes
its image line and kernel hyperplane; the unique Sylow-invariant flag identifies
these with the first and last cuts. The complementary endpoint parabolic
therefore generates with that centralizer. In dimensions four and five its
literal two-core quotient is S₃ × S₃, and every Sylow-preserving automorphism
fixes it, including graph automorphisms. Its two-core is self-centralizing.

The symmetric-cut argument reuses the proof of `InvariantParabolicPair` with
the actual centralizer marking retained. Source: Aschbacher--Smith 15.1.22(7),
printed pp.1099--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem transvection_commuting {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {w : V} {f : V →ₗ[ZMod 2] ZMod 2} (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0)
    (g : BinaryLinear.GL V) :
    transvection w f hfw * g = g * transvection w f hfw ↔
      g w = w ∧ ∀ v, f (g v) = f v := by
  constructor
  · intro he
    have hc (v : V) : f (g v) • w = f v • g w := by
      have hh := congrArg (fun a : BinaryLinear.GL V => a v) he
      change g v + f (g v) • w = g (v + f v • w) at hh
      simpa only [map_add,map_smul,add_right_inj] using hh
    obtain ⟨v,hv⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
    have hh := hc v
    rw [hv,one_smul] at hh
    have hne : f (g v) ≠ 0 := by
      intro hz
      rw [hz,zero_smul] at hh
      exact hw (g.map_eq_zero_iff.mp hh.symm)
    have hone : f (g v) = 1 := (by decide : ∀ a : ZMod 2,a ≠ 0 → a=1) _ hne
    have hgw : g w = w := by simpa only [hone,one_smul] using hh.symm
    refine ⟨hgw,fun x => ?_⟩
    have hh := hc x
    rw [hgw] at hh
    exact (smul_left_injective _ hw) hh
  · rintro ⟨hgw,hgf⟩
    ext v
    change g v + f (g v) • w = g (v + f v • w)
    rw [map_add,map_smul,hgw,hgf]

private theorem transvection_centralizer_flag {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {w : V} {f : V →ₗ[ZMod 2] ZMod 2} (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0) :
    centralizer ({transvection w f hfw} : Set (BinaryLinear.GL V)) =
      parabolic (Submodule.span (ZMod 2) {w}) ⊓ parabolic f.ker := by
  ext g
  rw [mem_centralizer_singleton_iff,eq_comm (a := g * transvection w f hfw),
    transvection_commuting hw hf hfw]
  constructor
  · rintro ⟨hgw,hgf⟩
    constructor
    · intro v
      constructor
      · rintro hv
        obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv
        apply Submodule.mem_span_singleton.mpr
        exact ⟨a,g.injective (by simpa only [map_smul,hgw] using ha)⟩
      · rintro hv
        obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [map_smul,hgw]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · intro v
      change f (g v) = 0 ↔ f v = 0
      rw [hgf]
  · rintro ⟨hW,hK⟩
    have hgw : g w = w := by
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp
        ((hW w).mpr (Submodule.mem_span_singleton_self _))
      have hane : a ≠ 0 := by
        intro hz
        rw [hz,zero_smul] at ha
        exact hw (g.map_eq_zero_iff.mp ha.symm)
      have ha1 : a = 1 := (by decide : ∀ a : ZMod 2,a ≠ 0 → a=1) _ hane
      simpa only [ha1,one_smul] using ha.symm
    refine ⟨hgw,fun v => ?_⟩
    have he : f (g v) = 0 ↔ f v = 0 := hK v
    by_cases hz : f v = 0
    · exact (he.mpr hz).trans hz.symm
    · have hgz := mt he.mp hz
      exact ((by decide : ∀ a : ZMod 2,a ≠ 0 → a=1) _ hgz).trans
        ((by decide : ∀ a : ZMod 2,a ≠ 0 → a=1) _ hz).symm

/-- The full-flag Sylow center centralizer is precisely its two endpoint cuts. -/
theorem sylow_center_centralizer_eq_endCuts {m : ℕ} (hm : 2 ≤ m)
    (S : Sylow 2 (LinearGroup (m+1))) (b : Basis m)
    (hb : (S : Subgroup (LinearGroup (m+1))) = cutStabilizer b Set.univ) :
    centralizer ((center (S : Subgroup (LinearGroup (m+1)))).map (S : Subgroup (LinearGroup (m+1))).subtype : Set (LinearGroup (m+1))) =
      cutStabilizer b {i | i.val = 0 ∨ i.val = m-1} := by
  let W := cutSpace b ⟨0,by omega⟩
  have hSW : (S : Subgroup (LinearGroup (m+1))) ≤ parabolic W := by
    rw [hb]
    intro x hx
    exact (mem_cutStabilizer b Set.univ x).mp hx _ (Set.mem_univ _)
  have hRS : radical W ≤ (S : Subgroup (LinearGroup (m+1))) := by
    have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' (radical_two W)
      (hSW.trans (parabolic_le_normalizer W))) le_sup_left
    exact he ▸ le_sup_right
  have hS : (S : Subgroup (LinearGroup (m+1))) ≠ ⊥ := by
    intro he
    exact radical_ne_bot (cutSpace_ne_bot b _) (cutSpace_ne_top b _) (bot_unique (he ▸ hRS))
  let : Nontrivial (S : Subgroup (LinearGroup (m+1))) := (Subgroup.nontrivial_iff_ne_bot _).mpr hS
  let : Nontrivial (center (S : Subgroup (LinearGroup (m+1)))) := S.isPGroup'.center_nontrivial
  obtain ⟨z,hz⟩ := exists_ne (1 : center (S : Subgroup (LinearGroup (m+1))))
  let t : LinearGroup (m+1) := z.val.val
  have ht : t ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext he))
  have hc : ∀ x ∈ S, x * t = t * x := fun x hx =>
    congrArg Subtype.val (mem_center_iff.mp z.property (⟨x,hx⟩ : S))
  have hc2 : Nat.card (center (S : Subgroup (LinearGroup (m+1)))) = 2 := by
    have hlo : 1 < Nat.card (center (S : Subgroup (LinearGroup (m+1)))) :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hhi : Nat.card (center (S : Subgroup (LinearGroup (m+1)))) ≤ 2 :=
      linear_sylow_center_card_le_two (by omega : 2 ≤ m+1) S
    omega
  obtain ⟨z0,hz0,hunique⟩ := (Nat.card_eq_two_iff' (1 : center (S : Subgroup (LinearGroup (m+1))))).mp hc2
  have he : centralizer ((center (S : Subgroup (LinearGroup (m+1)))).map (S : Subgroup (LinearGroup (m+1))).subtype : Set (LinearGroup (m+1))) =
      centralizer ({t} : Set (LinearGroup (m+1))) := by
    apply le_antisymm
    · exact centralizer_le (Set.singleton_subset_iff.mpr (mem_map_of_mem _ z.property))
    · intro g hg
      apply mem_centralizer_iff.mpr
      rintro x ⟨y,hy,rfl⟩
      by_cases hy1 : (⟨y,hy⟩ : center (S : Subgroup (LinearGroup (m+1)))) = 1
      · have hy1' : (y : LinearGroup (m+1)) = 1 := congrArg (fun u : center (S : Subgroup (LinearGroup (m+1))) => u.val.val) hy1
        change (y : LinearGroup (m+1)) * g = g * y
        simp only [hy1',mul_one,one_mul]
      · have hyz : (⟨y,hy⟩ : center (S : Subgroup (LinearGroup (m+1)))) = z :=
          (hunique _ hy1).trans (hunique _ hz).symm
        have hyz' := congrArg (fun u : center (S : Subgroup (LinearGroup (m+1))) => u.val.val) hyz
        change (y : LinearGroup (m+1)) * g = g * y
        change (y : LinearGroup (m+1)) = t at hyz'
        rw [hyz']
        exact (mem_centralizer_singleton_iff.mp hg).symm
  obtain ⟨w,f,hw,hf,hfw,hτ⟩ := central_sylow_eq_transvection
    (by rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod];
        exact dvd_pow_self 2 (by simp [Space]))
    (by simp [Space]; omega) S ht hc
  have htτ : t = transvection w f hfw := LinearEquiv.ext hτ
  have hSF : (S : Subgroup (LinearGroup (m+1))) ≤ centralizer ({transvection w f hfw} : Set _) := by
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    rw [← htτ]
    exact hc g hg
  rw [transvection_centralizer_flag hw hf hfw] at hSF
  have hW0 : Submodule.span (ZMod 2) {w} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hw
  have hW1 : Submodule.span (ZMod 2) {w} ≠ ⊤ := by
    intro he
    have hh : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) = 1 := finrank_span_singleton hw
    rw [he,finrank_top] at hh
    simp only [Space,Module.finrank_pi,Fintype.card_fin] at hh
    omega
  obtain ⟨i,hi⟩ := fullFlag_invariant_subspace b _ hW0 hW1 (hb ▸ hSF.trans inf_le_left)
  have hi0 : i.val = 0 := by
    have hh : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) = 1 := finrank_span_singleton hw
    rw [hi,cutSpace_finrank] at hh
    omega
  have hkdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hK0 : f.ker ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hkdim
    simp [Space] at hkdim
    omega
  have hK1 : f.ker ≠ ⊤ := fun he => hf (LinearMap.ker_eq_top.mp he)
  obtain ⟨j,hj⟩ := fullFlag_invariant_subspace b _ hK0 hK1 (hb ▸ hSF.trans inf_le_right)
  have hjm : j.val = m-1 := by
    rw [hj,cutSpace_finrank] at hkdim
    simp only [Space,Module.finrank_pi,Fintype.card_fin] at hkdim
    omega
  rw [he,htτ,transvection_centralizer_flag hw hf hfw,hi,hj]
  ext g
  rw [mem_inf,mem_cutStabilizer]
  constructor
  · rintro ⟨hgi,hgj⟩ k (hk | hk)
    · have hk' : k = i := Fin.ext (hk.trans hi0.symm)
      change g ∈ parabolic (cutSpace b k)
      rw [hk']
      exact hgi
    · have hk' : k = j := Fin.ext (hk.trans hjm.symm)
      change g ∈ parabolic (cutSpace b k)
      rw [hk']
      exact hgj
  · intro hg
    exact ⟨hg i (.inl hi0),hg j (.inr hjm)⟩

private theorem graph_fixes_symmetric_cuts {m : ℕ} (b : Basis m)
    (g : LinearGroup (m+1))
    (hB : (cutStabilizer b Set.univ).map
      (graphLinear (m+1) * MulAut.conj g).toMonoidHom = cutStabilizer b Set.univ)
    (cuts : Set (Fin m)) (hc : ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts) :
    (cutStabilizer b cuts).map (graphLinear (m+1) * MulAut.conj g).toMonoidHom =
      cutStabilizer b cuts := by
  let a := graphLinear (m+1) * MulAut.conj g
  have hp (j : Fin m) : (parabolic (cutSpace b j)).map a.toMonoidHom =
      parabolic (cutSpace b j.rev) := by
    rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g hB]
  ext x
  change x ∈ (cutStabilizer b cuts).map a.toMonoidHom ↔ x ∈ cutStabilizer b cuts
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  have hm (j : Fin m) : a.symm x ∈ parabolic (cutSpace b j) ↔
      x ∈ parabolic (cutSpace b j.rev) := by
    rw [← hp j, Subgroup.mem_map_equiv]
  constructor
  · intro hx j hj
    have he := (hm j.rev).mp (hx j.rev ((hc j).mpr hj))
    change x ∈ parabolic (cutSpace b j)
    simpa only [Fin.rev_rev] using he
  · intro hx j hj
    exact (hm j).mpr (hx j.rev ((hc j).mpr hj))

private theorem automorphism_fixes_symmetric_cuts {m : ℕ}
    (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (b : Basis m)
    (cuts : Set (Fin m)) (hc : ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts)
    (a : MulAut (LinearGroup (m+1)))
    (hB : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ) :
    (cutStabilizer b cuts).map a.toMonoidHom = cutStabilizer b cuts := by
  obtain ⟨g, rfl | rfl⟩ := smallDimension_inner_graph (by omega) (by omega) a
  · exact inner_fixes_cutStabilizer b g hB cuts
  · exact graph_fixes_symmetric_cuts b g hB cuts hc

private theorem cuts_ne_top {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (hc : cuts.Nonempty) : cutStabilizer b cuts ≠ ⊤ := by
  intro he
  obtain ⟨i,hi⟩ := hc
  have ht : cutStabilizer b ∅ ≤ cutStabilizer b cuts := by rw [he]; exact le_top
  exact ((cutStabilizer_le_iff b ∅ cuts).mp ht hi)

private theorem complementary_cuts_generate {m : ℕ} (hm : 1 ≤ m)
    (b : Basis m) (cuts : Set (Fin m)) :
    cutStabilizer b cuts ⊔ cutStabilizer b cutsᶜ = ⊤ := by
  apply top_unique
  rw [← iSup_minimalParabolic_eq_top hm b]
  apply iSup_le
  intro i
  by_cases hi : i ∈ cuts
  · apply le_trans _ le_sup_right
    apply (cutStabilizer_le_iff b {i}ᶜ cutsᶜ).mpr
    intro j hj he
    exact hj (he ▸ hi)
  · apply le_trans _ le_sup_left
    apply (cutStabilizer_le_iff b {i}ᶜ cuts).mpr
    intro j hj he
    exact hi (he ▸ hj)

/-- The endpoint parabolic is invariant under the entire Sylow stabilizer,
has the literal S₃ × S₃ quotient, and generates with the Sylow-center centralizer. -/
theorem exists_endpoint_parabolic {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (LinearGroup n)) :
    ∃ Q : Subgroup (LinearGroup n), (S : Subgroup _) ≤ Q ∧ Q ≠ ⊤ ∧
      Nonempty ((Q ⧸ pCore 2 Q) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      (∀ a : MulAut (LinearGroup n), (S : Subgroup _).map a.toMonoidHom = S →
        Q.map a.toMonoidHom = Q) ∧
      centralizer ((center (S : Subgroup (LinearGroup n))).map
        (S : Subgroup (LinearGroup n)).subtype : Set (LinearGroup n)) ⊔ Q = ⊤ := by
  have aux {m : ℕ} (hm : 3 ≤ m) (hm' : m ≤ 4)
      (S : Sylow 2 (LinearGroup (m+1))) (b : Basis m)
      (hb : (S : Subgroup _) = cutStabilizer b Set.univ) :
      let cuts : Set (Fin m) := {i | i.val=0 ∨ i.val=m-1}
      (S : Subgroup _) ≤ cutStabilizer b cutsᶜ ∧ cutStabilizer b cutsᶜ ≠ ⊤ ∧
      (∀ a : MulAut (LinearGroup (m+1)), (S : Subgroup _).map a.toMonoidHom = S →
        (cutStabilizer b cutsᶜ).map a.toMonoidHom = cutStabilizer b cutsᶜ) ∧
      centralizer ((center (S : Subgroup (LinearGroup (m+1)))).map
        (S : Subgroup (LinearGroup (m+1))).subtype : Set (LinearGroup (m+1))) ⊔
          cutStabilizer b cutsᶜ = ⊤ := by
    dsimp only
    refine ⟨?_,?_,?_,?_⟩
    · rw [hb]
      exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
    · apply cuts_ne_top
      exact ⟨⟨1,by omega⟩,by change ¬(1=0 ∨ 1=m-1); omega⟩
    · intro a ha
      apply automorphism_fixes_symmetric_cuts (by omega) hm' b _ _ a (hb ▸ ha)
      intro i
      simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,Fin.val_rev]
      have hi := i.isLt
      omega
    · rw [sylow_center_centralizer_eq_endCuts (by omega) S b hb]
      exact complementary_cuts_generate (by omega) b _
  rcases hn with rfl | rfl
  · obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer (m := 3) S
    obtain ⟨hSQ,hQ,hinv,hgen⟩ := aux (by decide) (by decide) S b hb
    let Q := cutStabilizer b {i : Fin 3 | i.val=0 ∨ i.val=3-1}ᶜ
    have he : Q = parabolic (cutSpace b 1) := by
      ext g
      rw [mem_cutStabilizer]
      constructor
      · intro h
        exact h 1 (by decide)
      · intro h i hi
        have hi1 : i = 1 := by fin_cases i <;> simp_all
        change g ∈ parabolic (cutSpace b i)
        rw [hi1]
        exact h
    let W := cutSpace b (1 : Fin 3)
    have hW : Module.finrank (ZMod 2) W = 2 := cutSpace_finrank b 1
    have hF : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
      have hh := W.finrank_quotient_add_finrank
      rw [hW] at hh
      simp [Space] at hh
      omega
    let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hW)
    let b' : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hF)
    let e := (SmallParabolicLevi.quotientTwoCoreEquivOfCoordinates W a b').trans
      (SmallParabolicLevi.linearTwoEquivSymmetricThree.prodCongr
        SmallParabolicLevi.linearTwoEquivSymmetricThree)
    exact ⟨Q,hSQ,hQ,he.symm ▸ ⟨e⟩,hinv,hgen⟩
  · obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer (m := 4) S
    obtain ⟨hSQ,hQ,hinv,hgen⟩ := aux (by decide) (by decide) S b hb
    let Q := cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=4-1}ᶜ
    have he : Q = FiveFlagGeometry.flagStabilizer b ({0,3} : Set (Fin 4))ᶜ := by
      change cutStabilizer b _ = cutStabilizer b _
      congr 1
      ext i
      fin_cases i <;> decide
    let e := (SmallParabolicLevi.TwoNodes.flagDiagonalQuotientEquiv b ({0,3} : Set (Fin 4))ᶜ).trans
      (SmallParabolicLevi.TwoNodes.pairFactorsEquiv 0 3 (Or.inl (by decide)))
    exact ⟨Q,hSQ,hQ,he.symm ▸ ⟨e⟩,hinv,hgen⟩

/-- Every proper Sylow overgroup in a binary linear group has characteristic
 two. This applies in particular to the endpoint parabolic above. -/
theorem proper_sylow_overgroup_generalizedFitting {m : ℕ}
    (S : Sylow 2 (LinearGroup (m+1))) (Q : Subgroup (LinearGroup (m+1)))
    (hSQ : (S : Subgroup _) ≤ Q) (hQ : Q ≠ ⊤) :
    Theory.GroupTheory.generalizedFitting Q = pCore 2 Q := by
  obtain ⟨b,cuts,hb,hcuts⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S Q hSQ
  have hc : cuts.Nonempty := by
    by_contra he
    have he' : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    apply hQ
    rw [hcuts,he',cutStabilizer]
    simp
  obtain ⟨i,hi⟩ := hc
  have hQP : Q ≤ parabolic (cutSpace b i) := by
    intro g hg
    exact (mem_cutStabilizer b cuts g).mp (hcuts ▸ hg) i hi
  exact Theory.GroupTheory.generalizedFitting_eq_pCore_of_sylow_overgroup S Q
    (parabolic (cutSpace b i)) hSQ hQP
    (centralizer_parabolic_twoCore_le (cutSpace_ne_bot b i) (cutSpace_ne_top b i))

end BinaryLinear.InvariantNodeActions
