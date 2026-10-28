module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Base

/-!
# Two representatives normalizing the intrinsic Sylow center

Every element of the certified Sylow subgroup has one of its 16384 binary
normal forms, by injectivity and the proved candidate order. If it is
central, its commutation with the first three generators on points 0 and 1
forces its index to be 0 or 6144. Representatives 839 and 840 commute with
normal form 6144 on the certified five-point base. They therefore centralize,
and hence normalize, the actual subgroup `centerImage fixedSylow`.

The finite calculations use only the previously certified point maps;
neither maximal coverage nor a max4/max6 order bound is used. The discovery
script is `source/CenterDiscovery.g`. Source application: Aschbacher--Smith,
printed p.511 (PDF p.528), citing Aschbacher (1986), no.343. See `Base` and
`Representatives` for the preserved ATLAS data and multiplication convention.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
open Subgroup Representatives RadicalCoverage.SylowCertificate
open LocalOrder

private theorem allNormalIndices (P : Fin 16384 → Prop) [DecidablePred P]
    (h : Rudvalis.Data.checkNat
      (fun k => decide (P ⟨k % 16384, Nat.mod_lt _ (by decide)⟩)) 16384 = true) :
    ∀ i, P i := by
  have hcheck (f : Nat → Bool) (n : Nat) :
      Rudvalis.Data.checkNat f n = true → ∀ k < n, f k = true := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Rudvalis.Data.checkNat, Bool.and_eq_true]
      rintro ⟨hn, hfn⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact ih hn k hlt
      · exact hfn
  rintro ⟨k, hk⟩
  have hp := of_decide_eq_true (hcheck _ _ h k hk)
  simpa only [Nat.mod_eq_of_lt hk] using hp

private def centerTest (n : Fin 16384) : Prop :=
  ∀ j : Fin 3, ∀ x : Fin 2,
    normalMap n (generatorMap (j.castLE (by decide)) (x.castLE (by decide))) =
      generatorMap (j.castLE (by decide)) (normalMap n (x.castLE (by decide)))

private instance (n : Fin 16384) : Decidable (centerTest n) :=
  by
  unfold centerTest
  infer_instance

set_option maxRecDepth 60000 in
private theorem center_index (n : Fin 16384) : centerTest n → n = 0 ∨ n = 6144 := by
  revert n
  apply allNormalIndices
  decide +kernel

private theorem normal_cover (g : candidate) :
    ∃ n : Fin 16384, candidateNormalForm n = (g : Model) := by
  let f : Fin 16384 → candidate := fun n => ⟨candidateNormalForm n, candidateNormalForm_mem n⟩
  have hi : Function.Injective f := fun _ _ h => normalForm_injective (congrArg Subtype.val h)
  have hs := (hi.bijective_of_nat_card_le (by rw [Nat.card_fin, candidate_card])).2
  obtain ⟨n, hn⟩ := hs g
  exact ⟨n, congrArg Subtype.val hn⟩

private theorem normal_zero : candidateNormalForm 0 = 1 := by
  simp [candidateNormalForm]

public theorem center_element_cases (g : Model) (hg : g ∈ centerImage fixedSylow) :
    g = 1 ∨ g = candidateNormalForm 6144 := by
  change g ∈ (center (sylowImage fixedSylow)).map (sylowImage fixedSylow).subtype at hg
  rw [sylowImage_fixedSylow] at hg
  obtain ⟨z, hz, rfl⟩ := hg
  obtain ⟨n, hn⟩ := normal_cover z
  have ht : centerTest n := by
    intro j x
    have hj : candidateGenerator (j.castLE (by decide)) ∈ candidate :=
      subset_closure ⟨j.castLE (by decide), rfl⟩
    have he := congrArg Subtype.val ((mem_center_iff.mp hz) ⟨_, hj⟩)
    change candidateGenerator (j.castLE (by decide)) * (z : Model) =
      (z : Model) * candidateGenerator (j.castLE (by decide)) at he
    rw [← hn] at he
    have hp := congrArg (fun a : Model => a • (x.castLE (by decide) : Fin 4060)) he
    simpa only [mul_smul, normal_smul, generator_smul] using hp.symm
  rcases center_index n ht with rfl | rfl
  · exact Or.inl (hn.symm.trans normal_zero)
  · exact Or.inr hn.symm

private theorem exceptional_commutes (i : Index) (hi : i = 839 ∨ i = 840) :
    candidateNormalForm 6144 * representative i = representative i * candidateNormalForm 6144 := by
  apply eq_of_five
  have hh : ∀ k : Fin 2, ∀ x : Fin 5,
      normalMap 6144 (representativeMap (if k = 0 then 839 else 840) (x.castLE (by decide))) =
      representativeMap (if k = 0 then 839 else 840) (normalMap 6144 (x.castLE (by decide))) := by
    decide +kernel
  intro x
  simp only [mul_smul, normal_smul, representative_smul]
  rcases hi with rfl | rfl
  · exact hh 0 x
  · exact hh 1 x

public theorem exceptional_center (i : Index) (hi : i = 839 ∨ i = 840) :
    representative i ∈ normalizer (centerImage fixedSylow : Set Model) := by
  apply centralizer_le_normalizer
  apply mem_centralizer_iff.mpr
  intro g hg
  rcases center_element_cases g hg with rfl | rfl
  · simp only [one_mul, mul_one]
  · exact exceptional_commutes i hi

end Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
