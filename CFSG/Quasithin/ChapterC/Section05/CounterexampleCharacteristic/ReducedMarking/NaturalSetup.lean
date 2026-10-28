module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.NaturalQuotient
/-!
# Constructing rank-one setup from the literal marked quotient

The actual Baumann Sylow subgroup contains the block-extension core. The
natural upper-root image gives its surjective parameter and exact action
kernel. Its central-cover projection supplies the action coordinates.
For a natural block, the full K-image lets every parameter be represented
inside S∩K, proving the required internality rather than assuming it.

Source: Aschbacher–Smith C.5.4, printed p.155.
-/
public section
open Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem setup_of_natural_quotient (K T : Subgroup G)
    (hblock : (∃ n, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 3)
    (hn : S T ≤ normalizer (K : Set G))
    (hsyl : Chapter1.IsSylowIn 2 (S T) (K ⊔ S T))
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd)
    (q : (K ⊔ S T : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) F)
    (π : U K →* Multiplicative (Fin 2 → F))
    (hq : Function.Surjective q) (hπ : Function.Surjective π)
    (hker : q.ker = (centralizer (U K : Set G)).subgroupOf (K ⊔ S T))
    (hπker : ∀ u, π u = 1 ↔ (u : G) ∈ centralizer (K : Set G))
    (himage : ((S T).subgroupOf (K ⊔ S T)).map q = upperUnipotent F)
    (hKimage : (K.subgroupOf (K ⊔ S T)).map q = ⊤ ∨ IsAlternatingBlock K 3)
    (he : ∀ (z : (K ⊔ S T : Subgroup G)) (u : U K),
      π (normalizerConjugate (inclusion (sup_le K.le_normalizer hn) z) u) = τ (q z) (π u)) :
    Nonempty (Setup T K F) := by
  let B := K ⊔ S T
  have hK : IsShort K := by
    rcases hblock with ⟨n,hn⟩ | ha
    · exact hn.2.1
    · exact ha.2.1
  obtain ⟨P,hP⟩ := hsyl
  have hQS : Q T K ≤ S T := hP ▸ pCoreIn_le_sylow B P
  have hSc : IsPGroup 2 (S T) := hP ▸ P.isPGroup'.map B.subtype
  have hc : B ⊓ centralizer (U K : Set G) = Q T K := normal_short_extension_centralizer K (S T) hK hSc hn
  have hUQ : U K ≤ Q T K := by
    let : IsElementaryAbelian 2 (U K) := hK.elementary.map K.subtype
    exact (le_inf ((map_subtype_le (blockU K)).trans le_sup_left)
      (le_centralizer (U K))).trans hc.le
  have hcore : Q T K = S T ⊓ centralizer (U K : Set G) :=
    le_antisymm (le_inf hQS (hc.ge.trans inf_le_right))
      ((le_inf (inf_le_left.trans le_sup_right) inf_le_right).trans hc.le)
  have hQB : q.ker ≤ (S T).subgroupOf B := by
    rw [hker]
    intro z hz
    exact hQS (hc.le ⟨z.property,hz⟩)
  have hnU : S T ≤ normalizer (U K : Set G) := hn.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  let a := q.comp (inclusion (show S T ≤ B from le_sup_right))
  have harange : a.range = upperUnipotent F := by
    calc
      _ = ((S T).subgroupOf B).map q := by
        ext z
        constructor
        · rintro ⟨s,rfl⟩; exact ⟨inclusion le_sup_right s,s.property,rfl⟩
        · rintro ⟨s,hs,rfl⟩; exact ⟨⟨s,hs⟩,rfl⟩
      _ = _ := himage
  let ueq := MonoidHom.ofInjective (upperUnipotentHom_injective F)
  let param : S T →* Multiplicative F := ueq.symm.toMonoidHom.comp
    (a.codRestrict (upperUnipotent F) (fun s => harange ▸ show a s ∈ a.range from ⟨s,rfl⟩))
  have hparam (s : S T) : upperUnipotentHom F (param s) = a s :=
    MonoidHom.apply_ofInjective_symm (upperUnipotentHom_injective F) _
  have hp : Function.Surjective param := by
    intro t
    obtain ⟨s,hs⟩ := (harange.symm ▸ (show upperUnipotentHom F t ∈ upperUnipotent F from ⟨t,rfl⟩) :
      upperUnipotentHom F t ∈ a.range)
    exact ⟨s,(upperUnipotentHom_injective F) ((hparam s).trans hs)⟩
  let c : ActionCoordinates T K F := {
    normalizes := hnU
    parameter := param
    parameter_surjective := hp
    parameter_kernel := by
      intro s
      rw [← (upperUnipotentHom_injective F).eq_iff,(upperUnipotentHom F).map_one,hparam]
      change inclusion (show S T ≤ B from le_sup_right) s ∈ q.ker ↔ _
      rw [hker]
      rfl
    projection := π
    projection_surjective := hπ
    projection_kernel := hπker
    equivariant := by
      intro s v
      have hh := he (inclusion (show S T ≤ B from le_sup_right) s) v
      change π (moduleConjugate hnU s v) = τ (a s) (π v) at hh
      rw [hh,← hparam,hτ]
      ext i
      fin_cases i <;> simp [upperUnipotentHom,transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two] }
  have hi (hk : (K.subgroupOf B).map q = ⊤) : c.IsInternal := by
    intro s
    obtain ⟨k,hk',hks⟩ := hk.symm ▸ (mem_top (a s))
    let sB := inclusion (show S T ≤ B from le_sup_right) s
    have hz : k * sB⁻¹ ∈ q.ker := by
      change q _ = 1
      rw [map_mul,map_inv,hks]
      exact mul_inv_cancel _
    have hkS : (k : G) ∈ S T := by
      have hh := (S T).mul_mem (hQB hz) s.property
      change (k : G) * (s : G)⁻¹ * (s : G) ∈ S T at hh
      simpa only [inv_mul_cancel_right] using hh
    refine ⟨⟨k,hkS⟩,hk',?_⟩
    apply upperUnipotentHom_injective F
    exact (hparam ⟨k,hkS⟩).trans (hks.trans (hparam s).symm)
  refine ⟨⟨c,?_,hUQ.trans hQS,hn,hcore,q,hq,?_,himage⟩⟩
  · rcases hKimage with hfull | ha
    · rcases hblock with ⟨n,hn⟩ | ha
      · exact Or.inl ⟨n,hn,hi hfull⟩
      · exact Or.inr ha
    · exact Or.inr ha
  · rw [hker]
    ext z
    exact ⟨fun hz => hc.le ⟨z.property,hz⟩,fun hz => (hc.ge hz).2⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
