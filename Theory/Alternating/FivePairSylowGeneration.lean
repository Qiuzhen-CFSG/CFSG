module
public import Theory.Alternating.FivePairBorelTorus
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.GroupTheory.SylowTwistedGeneratingPair

/-!
# Two Sylow conjugates generate the A₅ square

A Sylow four-group of A₅ has a unique maximal overgroup and is not normal,
so it and an inner conjugate generate A₅. The Sylow of a direct square is
the product of its projections. Choose a generating conjugate in each
factor and retain their pair as the conjugator of the original Sylow.
The marked transport returns the conjugator in the original group.

Source application: Aschbacher--Smith 8.3.12, printed p.726,
refs/quasithin.pdf, before the two-conjugate dimension bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive
local notation "A5" => alternatingGroup (Fin 5)

private theorem single_two_conjugates (S : Sylow 2 A5) :
    ∃ g : A5, (S : Subgroup A5) ⊔ (S : Subgroup A5).map (MulAut.conj g).toMonoidHom = ⊤ := by
  apply exists_conjugate_sup_eq_top_of_uniqueMaximal S
    (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_unique S)
  intro hn
  have htop : normalizer (S : Set A5) = ⊤ := @normalizer_eq_top _ _ _ hn
  have hcard := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card S
  rw [htop,Nat.card_congr (Subgroup.topEquiv).toEquiv,nat_card_alternatingGroup] at hcard
  norm_num [Nat.factorial] at hcard

private theorem pair_product (P : Sylow 2 (A5 × A5)) :
    ∃ Q R : Sylow 2 A5, (P : Subgroup (A5 × A5)) = (Q : Subgroup A5).prod (R : Subgroup A5) := by
  let Q := P.mapSurjective (f := MonoidHom.fst A5 A5) (fun x => ⟨(x,1),rfl⟩)
  let R := P.mapSurjective (f := MonoidHom.snd A5 A5) (fun x => ⟨(1,x),rfl⟩)
  have hp : IsPGroup 2 ((Q : Subgroup A5).prod (R : Subgroup A5)) := by
    obtain ⟨a,ha⟩ := Q.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := R.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+b)
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add]
  refine ⟨Q,R,(P.is_maximal' hp ?_).symm⟩
  intro x hx
  exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

/-- Two inner conjugates of any Sylow two-subgroup generate the actual A₅ square. -/
theorem pair_two_conjugates (P : Sylow 2 (A5 × A5)) :
    ∃ g : A5 × A5, (P : Subgroup (A5 × A5)) ⊔
      (P : Subgroup (A5 × A5)).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨Q,R,hP⟩ := pair_product P
  obtain ⟨a,ha⟩ := single_two_conjugates Q
  obtain ⟨b,hb⟩ := single_two_conjugates R
  let J := (P : Subgroup (A5 × A5)) ⊔ (P : Subgroup (A5 × A5)).map (MulAut.conj (a,b)).toMonoidHom
  have hleft : (⊤ : Subgroup A5) ≤ J.comap (MonoidHom.inl A5 A5) := by
    rw [←ha]
    apply sup_le
    · intro x hx
      exact mem_sup_left (hP.symm ▸ (show (x,1) ∈ (Q : Subgroup A5).prod (R : Subgroup A5) from ⟨hx,R.one_mem⟩))
    · rintro _ ⟨x,hx,rfl⟩
      change (a*x*a⁻¹,1) ∈ J
      have hxP : (x,1) ∈ (P : Subgroup (A5 × A5)) := hP.symm ▸ ⟨hx,R.one_mem⟩
      have h := mem_sup_right (S := (P : Subgroup (A5 × A5)))
        (mem_map_of_mem (MulAut.conj (a,b)).toMonoidHom hxP)
      change (a*x*a⁻¹,b*1*b⁻¹) ∈ J at h
      simpa only [mul_one,mul_inv_cancel] using h
  have hright : (⊤ : Subgroup A5) ≤ J.comap (MonoidHom.inr A5 A5) := by
    rw [←hb]
    apply sup_le
    · intro x hx
      exact mem_sup_left (hP.symm ▸ (show (1,x) ∈ (Q : Subgroup A5).prod (R : Subgroup A5) from ⟨Q.one_mem,hx⟩))
    · rintro _ ⟨x,hx,rfl⟩
      change (1,b*x*b⁻¹) ∈ J
      have hxP : (1,x) ∈ (P : Subgroup (A5 × A5)) := hP.symm ▸ ⟨Q.one_mem,hx⟩
      have h := mem_sup_right (S := (P : Subgroup (A5 × A5)))
        (mem_map_of_mem (MulAut.conj (a,b)).toMonoidHom hxP)
      change (a*1*a⁻¹,b*x*b⁻¹) ∈ J at h
      simpa only [mul_one,mul_inv_cancel] using h
  refine ⟨(a,b),top_unique ?_⟩
  rintro ⟨x,y⟩ _
  have h := J.mul_mem (hleft (mem_top x)) (hright (mem_top y))
  simpa only [MonoidHom.inl_apply,MonoidHom.inr_apply,Prod.mul_def,mul_one,one_mul] using h

/-- The two generating conjugates remain inside the marked original group. -/
theorem two_conjugates_of_pair_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* A5 × A5) (S : Sylow 2 G) :
    ∃ g : G, (S : Subgroup G) ⊔ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨g,hg⟩ := pair_two_conjugates (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨e.symm g,?_⟩
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup,map_top_of_surjective _ e.surjective]
  change (S : Subgroup G).map e.toMonoidHom ⊔ _ = _
  rw [map_map]
  have he : e.toMonoidHom.comp (MulAut.conj (e.symm g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change e (e.symm g * x * (e.symm g)⁻¹) = g * e x * g⁻¹
    rw [map_mul,map_mul,map_inv,e.apply_symm_apply]
  rw [he,←map_map]
  exact hg
end Theory.AlternatingFive
