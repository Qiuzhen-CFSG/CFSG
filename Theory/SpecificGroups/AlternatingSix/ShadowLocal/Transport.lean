module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# Transport through the actual conjugation action on A₆

For K normal in H and an equivalence K ≃ A₆, transport conjugation to
a homomorphism H → Aut(A₆). Its kernel is exactly C_H(K), its image on
K is Inn(A₆), and the preimage of Inn(A₆) is K C_H(K). The first
isomorphism theorem therefore gives a compatible quotient equivalence
when the action is surjective. Subgroups disjoint from the centralizer
embed through this same map; fixed groups are the actual centralizers
inside K, and Sylow subgroups map to Sylow subgroups.

Source: the quotient-action arguments in Aschbacher–Smith, *The
Classification of Quasithin Groups*, printed pp.567–570. Here normality
is inside H, so callers may take H to be the source local overgroup.
-/

@[expose] public section

namespace AlternatingSix.ShadowLocal

open Subgroup

variable {H : Type*} [Group H] (K : Subgroup H) [K.Normal] (e : K ≃* A6)

def conjugationAction : H →* AutA6 :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))

theorem conjugationAction_apply (h : H) (k : K) :
    conjugationAction K e h (e k) = e (MulAut.conjNormal h k) := by
  simp [conjugationAction, MulAut.congr]

theorem eq_conjugationAction_of_compatible (a : H →* AutA6)
    (ha : ∀ (h : H) (k : K), a h (e k) = e (MulAut.conjNormal h k)) :
    a = conjugationAction K e := by
  apply MonoidHom.ext
  intro h
  apply MulEquiv.ext
  intro k
  obtain ⟨k, rfl⟩ := e.surjective k
  exact (ha h k).trans (conjugationAction_apply K e h k).symm

theorem conjugationAction_on_inner (k : K) :
    conjugationAction K e (k : H) = MulAut.conj (e k) := by
  ext a
  simp [conjugationAction, MulAut.congr, MulAut.conjNormal_val]

theorem conjugationAction_map_inner : K.map (conjugationAction K e) = inner := by
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e ⟨k, hk⟩, (conjugationAction_on_inner K e ⟨k, hk⟩).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(e.symm a : H), (e.symm a).property, ?_⟩
    simpa using conjugationAction_on_inner K e (e.symm a)

theorem conjugationAction_ker :
    (conjugationAction K e).ker = centralizer (K : Set H) := by
  rw [conjugationAction, MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective]
  ext h
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro he k hk
    have he' := congrArg (fun f : MulAut K => (f ⟨k, hk⟩ : H)) he
    change h * k * h⁻¹ = k at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro he
    ext k
    change h * (k : H) * h⁻¹ = (k : H)
    rw [← he k k.property, mul_inv_cancel_right]

theorem conjugationAction_preimage_inner :
    inner.comap (conjugationAction K e) = K ⊔ centralizer (K : Set H) := by
  rw [← conjugationAction_map_inner K e, Subgroup.comap_map_eq, conjugationAction_ker]

noncomputable def faithfulSubgroupEquiv (X : Subgroup H)
    (hX : Disjoint X (centralizer (K : Set H))) :
    X ≃* X.map (conjugationAction K e) :=
  MulEquiv.ofBijective ((conjugationAction K e).subgroupMap X)
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
        conjugationAction_ker, Subgroup.subgroupOf_eq_bot]
      exact hX.symm,
    (conjugationAction K e).subgroupMap_surjective X⟩

theorem faithfulSubgroupEquiv_apply (X : Subgroup H)
    (hX : Disjoint X (centralizer (K : Set H))) (x : X) :
    (faithfulSubgroupEquiv K e X hX x : AutA6) = conjugationAction K e x := rfl

noncomputable def conjugationQuotientEquiv
    (hsurj : Function.Surjective (conjugationAction K e)) :
    H ⧸ centralizer (K : Set H) ≃* AutA6 :=
  (QuotientGroup.quotientMulEquivOfEq (conjugationAction_ker K e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)

theorem conjugationQuotientEquiv_mk
    (hsurj : Function.Surjective (conjugationAction K e)) (h : H) :
    conjugationQuotientEquiv K e hsurj (QuotientGroup.mk' _ h) =
      conjugationAction K e h := rfl

theorem mem_centralizer_iff_action_fixed (h : H) (k : K) :
    (k : H) ∈ centralizer ({h} : Set H) ↔
      conjugationAction K e h (e k) = e k := by
  rw [conjugationAction_apply, e.injective.eq_iff]
  rw [mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Subtype.ext_iff]
  change h * (k : H) = (k : H) * h ↔ h * (k : H) * h⁻¹ = (k : H)
  exact mul_inv_eq_iff_eq_mul.symm

def fixedCentralizerEquiv (h : H) :
    (centralizer ({h} : Set H)).subgroupOf K ≃*
      GLS3.Chapter5.automorphismFixedSubgroup (conjugationAction K e h) where
  toFun k := ⟨e k.val, (mem_centralizer_iff_action_fixed K e h k.val).mp k.property⟩
  invFun a := ⟨e.symm a.val, (mem_centralizer_iff_action_fixed K e h (e.symm a.val)).mpr
    (by simpa only [e.apply_symm_apply] using
      (show conjugationAction K e h a.val = a.val from a.property))⟩
  left_inv k := by ext; simp
  right_inv a := by ext; simp
  map_mul' k l := Subtype.ext (e.map_mul k.val l.val)

variable [Finite H]

def conjugationSylow (hsurj : Function.Surjective (conjugationAction K e))
    (S : Sylow 2 H) : Sylow 2 AutA6 := S.mapSurjective hsurj

theorem conjugationSylow_coe (hsurj : Function.Surjective (conjugationAction K e))
    (S : Sylow 2 H) :
    (conjugationSylow K e hsurj S : Subgroup AutA6) =
      (S : Subgroup H).map (conjugationAction K e) := rfl

theorem conjugationSylow_card (hsurj : Function.Surjective (conjugationAction K e))
    (S : Sylow 2 H) :
    Nat.card ((S : Subgroup H).map (conjugationAction K e)) = 32 :=
  sylow_card (conjugationSylow K e hsurj S)

end AlternatingSix.ShadowLocal
