module

public import Theory.GroupTheory.PStar.Defs
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Elementary properties of p-star groups

Surjections preserve the p-star condition: lift a Sylow subgroup to the
normal preimage, then map the defining centralizer supplement. Normal
p-subgroups are central because their centralizer has p-group quotient,
which is trivial by p-perfectness. Groups of order prime to p are p-star.

Source: GLS II, Chapter B, Lemma 5.2(i), (ii), and the first clause of (iv).
The residual is O^p throughout; centralizers use the embedded Sylow subgroup.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-- A surjective image of a finite p-star group is p-star. -/
theorem IsPStar.of_surjective [Finite G] [Fact p.Prime]
    (hG : IsPStar p G) (f : G →* H) (hf : Function.Surjective f) :
    IsPStar p H := by
  refine ⟨(pResidual_eq_top_iff p H).mpr
    (((pResidual_eq_top_iff p G).mp hG.1).of_surjective f hf), ?_⟩
  intro N hN P
  let M := N.comap f
  let g : M →* N :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : G) (y : G)) }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, by change f x ∈ N; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hg p P
  have hQP : ((Q : Subgroup M).map M.subtype).map f =
      (P : Subgroup N).map N.subtype := by
    have h := congrArg (fun S : Sylow p N => (S : Subgroup N).map N.subtype) hQ
    have he : N.subtype.comp g = f.comp M.subtype := by ext x; rfl
    simpa only [Sylow.coe_mapSurjective, Subgroup.map_map, he] using h
  have hc := Subgroup.map_centralizer_le_centralizer_image
    (((Q : Subgroup M).map M.subtype) : Set G) f
  have hgen := congrArg (fun S : Subgroup G => S.map f) (hG.2 M Q)
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective f hf] at hgen
  apply top_unique
  rw [← hgen]
  apply sup_le_sup
  · exact Subgroup.map_comap_le f N
  · simpa only [← Subgroup.coe_map, hQP] using hc

/-- Quotient closure, GLS II 5.2(ii). -/
theorem IsPStar.quotient [Finite G] [Fact p.Prime] (hG : IsPStar p G)
    (N : Subgroup G) [N.Normal] : IsPStar p (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Invariance under a genuine group isomorphism. -/
theorem IsPStar.of_equiv [Finite G] [Fact p.Prime] (hG : IsPStar p G)
    (e : G ≃* H) : IsPStar p H :=
  hG.of_surjective e.toMonoidHom e.surjective

/-- Normal p-subgroups of a p-star group are central, GLS II 5.2(iv). -/
theorem IsPStar.normal_pSubgroup_le_center (hG : IsPStar p G)
    (N : Subgroup G) [N.Normal] (hNp : IsPGroup p N) : N ≤ center G := by
  let P : Sylow p N :=
    { toSubgroup := ⊤
      isPGroup' := hNp.to_subgroup ⊤
      is_maximal' := fun _ h => top_unique h }
  have hgen : N ⊔ centralizer (N : Set G) = ⊤ := by
    have ht : (⊤ : Subgroup N).map N.subtype = N := by
      ext x
      simp
    simpa only [P, ht] using hG.2 N P
  have hq := Subgroup.isPGroup_quotient_of_sup_eq_top
    (centralizer (N : Set G)) N hNp (sup_comm N _ ▸ hgen)
  have hc : centralizer (N : Set G) = ⊤ :=
    (pResidual_eq_top_iff p G).mp hG.1 _ inferInstance hq
  exact Subgroup.centralizer_eq_top_iff_subset.mp hc

/-- Groups of order prime to p satisfy the p-star definition, GLS II 5.2(i). -/
theorem isPStar_of_coprime_card [Finite G] [Fact p.Prime]
    (hcard : Nat.Coprime p (Nat.card G)) : IsPStar p G := by
  refine ⟨top_unique (fun x _ => mem_pResidual_of_orderOf_coprime
    (hcard.of_dvd_right (orderOf_dvd_natCard x))), ?_⟩
  intro N _ P
  let S := (P : Subgroup N).map N.subtype
  have hpS : IsPGroup p S := P.isPGroup'.map N.subtype
  obtain ⟨n, hn⟩ := hpS.exists_card_eq
  have hS : S = ⊥ := S.eq_bot_of_card_eq
    (Nat.eq_one_of_dvd_coprimes (hcard.pow_left n) (by rw [hn]) S.card_subgroup_dvd_card)
  change N ⊔ centralizer (S : Set G) = ⊤
  have hc : centralizer (S : Set G) = ⊤ :=
    centralizer_eq_top_iff_subset.mpr (show S ≤ center G by rw [hS]; exact bot_le)
  rw [hc, sup_top_eq]

/-- A p-star p-group is trivial. -/
theorem IsPStar.subsingleton_of_isPGroup (hG : IsPStar p G)
    (hpG : IsPGroup p G) : Subsingleton G := by
  have hb : (⊥ : Subgroup G) = ⊤ :=
    (pResidual_eq_top_iff p G).mp hG.1 ⊥ inferInstance (hpG.to_quotient ⊥)
  exact ⟨fun x y => by
    have hx : x = 1 := mem_bot.mp (hb ▸ mem_top x)
    have hy : y = 1 := mem_bot.mp (hb ▸ mem_top y)
    exact hx.trans hy.symm⟩

end Theory.GroupTheory
