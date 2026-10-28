module
public import Theory.SpecificGroups.BinaryLinear.EndpointParabolic

/-!
# Generation by an outer-invariant binary parabolic

In dimensions four and five, every Sylow overgroup is a partial flag
stabilizer. The Sylow-center centralizer retains exactly the two endpoint
cuts. An outer automorphism fixing the Sylow reverses the flag, so an
invariant overgroup escaping any subgroup containing that centralizer must
omit both endpoint cuts. The two overgroups therefore generate the full
linear group. This applies to the original local intersections in the
ordinary graph-action case of Aschbacher--Smith 15.1.22(7), printed
pp.1099--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

private theorem minimal_le_cuts {m : ℕ} (b : Basis m) (cuts : Set (Fin m)) (i : Fin m) :
    minimalParabolic b i ≤ cutStabilizer b cuts ↔ i ∉ cuts := by
  rw [minimalParabolic,cutStabilizer_le_iff]
  constructor
  · intro h hi
    exact h hi rfl
  · intro hi j hj he
    exact hi (he ▸ hj)

private theorem fixed_cuts_rev {m : ℕ} (hm : 2 ≤ m) (hm' : m ≤ 4)
    (b : Basis m) (cuts : Set (Fin m)) (a : MulAut (LinearGroup (m+1)))
    (ha : a ∉ MulAut.innerSubgroup _)
    (hS : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ)
    (hK : (cutStabilizer b cuts).map a.toMonoidHom = cutStabilizer b cuts)
    {i : Fin m} (hi : i ∉ cuts) : i.rev ∉ cuts := by
  apply (minimal_le_cuts b cuts i.rev).mp
  rw [←outer_reverses_minimalParabolic hm hm' b a ha hS i,←hK]
  exact map_mono ((minimal_le_cuts b cuts i).mpr hi)

/-- A Sylow overgroup invariant under an outer automorphism and escaping H
generates with H whenever H contains the Sylow-center centralizer. -/
theorem outer_invariant_escape_generates {m : ℕ} (hm : 3 ≤ m) (hm' : m ≤ 4)
    (S : Sylow 2 (LinearGroup (m+1))) (H K : Subgroup (LinearGroup (m+1)))
    (hSH : (S : Subgroup _) ≤ H) (hSK : (S : Subgroup _) ≤ K)
    (hC : centralizer ((center (S : Subgroup (LinearGroup (m+1)))).map
      (S : Subgroup (LinearGroup (m+1))).subtype : Set (LinearGroup (m+1))) ≤ H)
    (hout : ¬K ≤ H) (a : MulAut (LinearGroup (m+1)))
    (ha : a ∉ MulAut.innerSubgroup _)
    (hS : (S : Subgroup _).map a.toMonoidHom = S)
    (hK : K.map a.toMonoidHom = K) : H ⊔ K = ⊤ := by
  classical
  obtain ⟨b,c,hb,hH⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S H hSH
  obtain ⟨b',k,_,hK'⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S K hSK
  have hk : K = cutStabilizer b k := hK'.trans
    (cutStabilizer_eq_of_fullFlag_le b b' k (by rwa [←hb,←hK']))
  rw [hH,hk] at hout ⊢
  rw [hb] at hS
  rw [hk] at hK
  rw [sylow_center_centralizer_eq_endCuts (by omega) S b hb,hH] at hC
  have hc : c ⊆ {i : Fin m | i.val=0 ∨ i.val=m-1} :=
    (cutStabilizer_le_iff _ _ _).mp hC
  have hn : ¬c ⊆ k := fun hh => hout ((cutStabilizer_le_iff _ _ _).mpr hh)
  obtain ⟨i,hi,hik⟩ := Set.not_subset.mp hn
  have hirev := fixed_cuts_rev (by omega) hm' b k a ha hS hK hik
  have hdis (j : Fin m) (hj : j ∈ c) : j ∉ k := by
    have hie := hc hi
    have hje := hc hj
    have he : j=i ∨ j=i.rev := by
      apply or_iff_not_imp_left.mpr
      intro hne
      apply Fin.ext
      have hne' : j.val ≠ i.val := fun hh => hne (Fin.ext hh)
      simp only [Set.mem_ofPred_eq] at hie hje
      simp only [Fin.val_rev]
      omega
    rcases he with rfl | rfl
    · exact hik
    · exact hirev
  apply top_unique
  rw [←iSup_minimalParabolic_eq_top (by omega) b]
  apply iSup_le
  intro j
  by_cases hj : j ∈ c
  · exact ((minimal_le_cuts b k j).mpr (hdis j hj)).trans le_sup_right
  · exact ((minimal_le_cuts b c j).mpr hj).trans le_sup_left

end BinaryLinear.InvariantNodeActions
