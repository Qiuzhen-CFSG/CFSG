module
public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive

/-!
# Exchanged catalogue summands and the low-rank clause

For G.11.2(8) the actual invariant A₇ four-space and its actor-conjugate
complement give swapping coordinates. Commutativity in the elementary actor
forces equal inner blocks; the four-dimensional A₇ rank calculation then
makes their total displacement zero or four. Odd elements exchange the blocks
and also move four dimensions.

For G.11.2(12), distinct components commute and their disjoint commutator
spaces force the second component to fix the first summand. The prescribed
orthogonal A₅ coordinates and the printed actor generation statement give the
same zero-or-four conclusion. Hence both rows exclude the nonzero witness of
rank at most two, including the rank-one possibility.

The proofs reuse the concrete rank and swapping-coordinate calculations from
`QuasithinRankTwoInvolutionExclusions.Imprimitive`. They adapt the literal
catalogue transports used in Chapter 6's strict-intersection consumer. Their
original Chapter 14 consumer is `source_large_fixed_line_remainder_of_mixed_size`.
Source: Aschbacher--Smith G.11.1(3ii), G.11.2(8,12), printed p.364.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
namespace CatalogueExchanged
open Representation.RankTwo Representation.RankTwo.Imprimitive
private theorem seven_rank
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (e : H ≃* Equiv.Perm (Fin 7))
    (P : Subrepresentation (ρ.comp
      (e.symm.toMonoidHom.comp (alternatingGroup (Fin 7)).subtype)))
    (hd : Module.finrank (ZMod 2) P.toSubmodule = 4)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hxodd : e x ∉ alternatingGroup (Fin 7))
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hsplit : IsCompl P.toSubmodule (P.toSubmodule.map (ρ x)))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 0 ∨
      Module.finrank (ZMod 2) (movedSpace ρ g) = 4 := by
  let σ := P.toRepresentation
  have hx2 : ρ x * ρ x = 1 := by rw [← map_mul, hX2 x hx, map_one]
  let f := swappedCoordinates (ρ x) hx2 P.toSubmodule hsplit
  have inner_action (b : H) (hb : b ∈ X) (heven : e b ∈ alternatingGroup (Fin 7))
      (v w : P.toSubmodule) :
      ρ b (f (v,w)) = f (σ ⟨e b, heven⟩ v, σ ⟨e b, heven⟩ w) := by
    apply action_swappedCoordinates (ρ x) hx2 P.toSubmodule hsplit
      (ρ b) (σ ⟨e b, heven⟩) ((hXcomm b hb x hx).map ρ)
    intro u
    change ρ b u = ρ (e.symm (e b)) u
    rw [e.symm_apply_apply]
  by_cases heven : e g ∈ alternatingGroup (Fin 7)
  · have ha : (⟨e g, heven⟩ : alternatingGroup (Fin 7)) * ⟨e g, heven⟩ = 1 := by
      apply Subtype.ext
      change e g * e g = 1
      rw [← map_mul, hX2 g hg, map_one]
    have hr := finrank_of_block_coordinates f (ρ g) (σ ⟨e g, heven⟩)
      (inner_action g hg heven)
    rcases AlternatingSeven.finrank_four_square_one σ hd ⟨e g, heven⟩ ha with h | h
    all_goals
      have hr' : Module.finrank (ZMod 2) (movedSpace ρ g) =
          2 * Module.finrank (ZMod 2) (movedSpace σ ⟨e g, heven⟩) := hr
      rw [h] at hr'
      omega
  · have hxsign : (e x).sign = -1 := (Int.units_eq_one_or (e x).sign).resolve_left hxodd
    have hgsign : (e g).sign = -1 := (Int.units_eq_one_or (e g).sign).resolve_left heven
    have hb : x * g ∈ X := X.mul_mem hx hg
    have hbeven : e (x * g) ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, hxsign, hgsign]
      decide
    have hge : g = x * (x * g) := by rw [← mul_assoc, hX2 x hx, one_mul]
    have hact (v w : P.toSubmodule) :
        ρ g (f (v,w)) = f (σ ⟨e (x*g), hbeven⟩ w, σ ⟨e (x*g), hbeven⟩ v) := by
      conv_lhs => rw [hge, map_mul, Module.End.mul_apply, inner_action (x*g) hb hbeven]
      exact swappedCoordinates_swap (ρ x) hx2 P.toSubmodule hsplit _ _
    have hr := finrank_of_exchanging_coordinates f (ρ g)
      (σ ⟨e (x*g), hbeven⟩) (σ ⟨e (x*g), hbeven⟩) hact
      (by rw [← map_mul, hX2 g hg, map_one])
    rw [hd] at hr
    exact Or.inr hr


private theorem seven_decomposition_rank
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (e : H ≃* Equiv.Perm (Fin 7))
    (P : Subrepresentation (ρ.comp
      (e.symm.toMonoidHom.comp (alternatingGroup (Fin 7)).subtype)))
    (hd : Module.finrank (ZMod 2) P.toSubmodule = 4)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hsplit : IsCompl P.toSubmodule (P.toSubmodule.map (ρ x)))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 0 ∨
      Module.finrank (ZMod 2) (movedSpace ρ g) = 4 := by
  apply seven_rank ρ e P hd X x hx ?_ hX2 hXcomm hsplit g hg
  intro heven
  have hzero : P.toSubmodule = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hinv : ρ x v ∈ P.toSubmodule := by
      have h := P.apply_mem_toSubmodule ⟨e x, heven⟩ hv
      change ρ (e.symm (e x)) v ∈ P.toSubmodule at h
      rwa [e.symm_apply_apply] at h
    have ht : ρ x v = 0 := hsplit.disjoint.le_bot ⟨hinv, ⟨v,hv,rfl⟩⟩
    have hh := congrArg (ρ x) ht
    change v = 0
    simpa only [← Module.End.mul_apply, ← map_mul, hX2 x hx, map_one,
      Module.End.one_apply, map_zero] using hh
  have hd0 : Module.finrank (ZMod 2) P.toSubmodule = 0 := Submodule.finrank_eq_zero.mpr hzero
  omega

open OrthogonalA5
private theorem five_source_rank
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (Alternating × Alternating) →* H)
    (P : Submodule (ZMod 2) V) (eP : P ≃ₗ[ZMod 2] Space)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hsplit : IsCompl P (P.map (ρ x)))
    (hfirst : ∀ p q (v : Space),
      ρ (i (p,q)) (eP.symm v : P) = (eP.symm (representation p v) : P))
    (hgen : X = Subgroup.zpowers x ⊔ (X ⊓ i.range))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 0 ∨
      Module.finrank (ZMod 2) (movedSpace ρ g) = 4 := by
  have hx2 : ρ x * ρ x = 1 := by rw [← map_mul, hX2 x hx, map_one]
  let f : (Space × Space) ≃ₗ[ZMod 2] V :=
    (eP.symm.prodCongr eP.symm).trans (swappedCoordinates (ρ x) hx2 P hsplit)
  have hswap (v w : Space) : ρ x (f (v,w)) = f (w,v) :=
    swappedCoordinates_swap (ρ x) hx2 P hsplit (eP.symm v) (eP.symm w)
  have hinner (p q : Alternating) (hb : i (p,q) ∈ X) (v w : Space) :
      ρ (i (p,q)) (f (v,w)) = f (representation p v, representation p w) := by
    change ρ (i (p,q)) ((eP.symm v : P) + ρ x (eP.symm w : P)) =
      (eP.symm (representation p v) : P) + ρ x (eP.symm (representation p w) : P)
    have hc (z : V) : ρ (i (p,q)) (ρ x z) = ρ x (ρ (i (p,q)) z) :=
      LinearMap.congr_fun ((hXcomm _ hb x hx).map ρ).eq z
    rw [map_add, hc, hfirst, hfirst]
  obtain ⟨b, hb, hgb⟩ := two_coset_normal_form X (X ⊓ i.range) x hx inf_le_left
    hX2 (fun g hg => hXcomm g hg x hx) hgen g hg
  obtain ⟨⟨p,q⟩, rfl⟩ := hb.2
  rcases hgb with rfl | rfl
  · let a := (representation p).prodMap (representation p)
    have ha2 : a * a = 1 := by
      apply LinearMap.ext
      intro z
      apply f.injective
      have h2 : ρ (i (p,q)) * ρ (i (p,q)) = 1 := by
        rw [← map_mul, hX2 _ hb.1, map_one]
      have he : ρ (i (p,q)) (ρ (i (p,q)) (f z)) = f z := LinearMap.congr_fun h2 (f z)
      rw [hinner p q hb.1 z.1 z.2, hinner p q hb.1] at he
      exact he
    have hc : Commute a (swap (LinearEquiv.refl (ZMod 2) Space)) := by
      apply LinearMap.ext
      rintro ⟨v,w⟩
      rfl
    have hr := (displacementRangeEquiv f a (ρ (i (p,q)))
      (fun z => hinner p q hb.1 z.1 z.2)).finrank_eq
    rcases finrank_wreathOperator p p false ha2 hc with h | h
    · exact Or.inl (hr.symm.trans h)
    · exact Or.inr (hr.symm.trans h)
  · have hact (v w : Space) :
        ρ (x * i (p,q)) (f (v,w)) = f (representation p w, representation p v) := by
      rw [map_mul, Module.End.mul_apply, hinner p q hb.1, hswap]
    have hr := finrank_of_exchanging_coordinates f (ρ (x * i (p,q)))
      (representation p) (representation p) hact (by rw [← map_mul, hX2 _ hg, map_one])
    rw [finrank_space] at hr
    exact Or.inr hr

open BinaryOffender
private theorem five_commutator_rank
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (Alternating × Alternating) →* H)
    (eP : (subspaceCommutator ρ ⊤
      (i.comp (MonoidHom.inl Alternating Alternating)).range) ≃ₗ[ZMod 2] Space)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hconj : ∀ p : Alternating, x * i (p,1) * x⁻¹ = i (1,p))
    (hsplit : IsCompl
      (subspaceCommutator ρ ⊤ (i.comp (MonoidHom.inl Alternating Alternating)).range)
      (subspaceCommutator ρ ⊤ (i.comp (MonoidHom.inr Alternating Alternating)).range))
    (hfirst : ∀ p (v : Space),
      ρ (i (p,1)) (eP.symm v : V) = (eP.symm (representation p v) : V))
    (hgen : X = Subgroup.zpowers x ⊔ (X ⊓ i.range))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 0 ∨
      Module.finrank (ZMod 2) (movedSpace ρ g) = 4 := by
  apply five_source_rank ρ i _ eP X x hx hX2 hXcomm ?_ ?_ hgen g hg
  · rwa [map_commutator_of_swaps_factors ρ i x (hX2 x hx) hconj]
  · intro p q v
    have hfix : ρ (i (1,q)) (eP.symm v : V) = (eP.symm v : V) := by
      apply fixes_commutator_of_disjoint ρ _ _ ?_ hsplit.disjoint
        (i (1,q)) ⟨q,rfl⟩ (eP.symm v) (eP.symm v).property
      rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
      exact (show Commute (a,1) (1,b) from by simp [Commute, SemiconjBy]).map i
    have he : i (p,q) = i (p,1) * i (1,q) := by rw [← map_mul]; simp
    rw [he, map_mul, Module.End.mul_apply, hfix, hfirst]

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V} {B : LinearMap.BilinForm (ZMod 2) V}
  {X : Subgroup H}
private theorem case_eight_rank [IsElementaryAbelian 2 X]
    (a : H) (ha : a ∈ X)
    (hc : ChapterG.Section11.CaseEight ρ B X) :
    finrank (ZMod 2) (movedSpace ρ a) = 0 ∨
      finrank (ZMod 2) (movedSpace ρ a) = 4 := by
  obtain ⟨_, ⟨e⟩, I, hI, _, hstable, x, hx, _, hsplit⟩ := hc
  have hA : IsComponent (Equiv.Perm (Fin 7)) (alternatingGroup (Fin 7)) := by
    refine ⟨(inferInstance : (alternatingGroup (Fin 7)).Normal).isSubnormal, ?_⟩
    change IsQuasisimple (alternatingGroup (Fin (2 + 5)))
    infer_instance
  have hle : (alternatingGroup (Fin 7)).map e.symm.toMonoidHom ≤ componentLayer H :=
    le_sSup (hA.map_equiv e.symm)
  let P : Subrepresentation (ρ.comp
      (e.symm.toMonoidHom.comp (alternatingGroup (Fin 7)).subtype)) := {
    toSubmodule := I
    apply_mem_toSubmodule := fun g w hw =>
      (hstable (hle (mem_map_of_mem e.symm.toMonoidHom g.property)) w).mpr hw }
  exact seven_decomposition_rank ρ e P hI X x hx
    (fun g hg => by simpa only [pow_two] using (show g ^ 2 = 1 from elemPow_eq_one_of_isElementaryAbelian g hg))
    (fun g hg k hk => show Commute g k from
      congrArg Subtype.val (mul_comm (⟨g, hg⟩ : X) ⟨k, hk⟩)) hsplit a ha

omit [FiniteDimensional (ZMod 2) V] in
private theorem case_twelve_rank [IsElementaryAbelian 2 X]
    (a : H) (ha : a ∈ X)
    (hc : ChapterG.Section11.CaseTwelve ρ X) :
    finrank (ZMod 2) (movedSpace ρ a) = 0 ∨
      finrank (ZMod 2) (movedSpace ρ a) = 4 := by
  open BinaryOffender in
  obtain ⟨_, L, hL, x, hx, _, hsplit, ⟨e, f, hf⟩, hgen, _⟩ := hc
  let Lx := L.map (MulAut.conj x).toMonoidHom
  have hne : L ≠ Lx := by
    intro heq
    have hh := hsplit.disjoint
    change Disjoint (BinaryOffender.subspaceCommutator ρ ⊤ L)
      (BinaryOffender.subspaceCommutator ρ ⊤ Lx) at hh
    rw [← heq] at hh
    have hz := disjoint_self.mp hh
    have hd := f.finrank_eq
    rw [hz, finrank_bot, Imprimitive.OrthogonalA5.finrank_space] at hd
    omega
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne (hL.map_equiv (MulAut.conj x)) hne)
  let j : alternatingGroup (Fin 5) →* H := L.subtype.comp e.symm.toMonoidHom
  let k : alternatingGroup (Fin 5) →* H := (MulAut.conj x).toMonoidHom.comp j
  have hj : j.range = L := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact (e.symm b).property
    · intro hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simp [j]
  have hk : k.range = Lx := by
    dsimp only [k]
    rw [MonoidHom.range_comp, hj]
  have hcomm (b c : alternatingGroup (Fin 5)) : Commute (j b) (k c) := by
    have hb : j b ∈ L := hj ▸ (show j b ∈ j.range from ⟨b, rfl⟩)
    have hc : k c ∈ Lx := hk ▸ (show k c ∈ k.range from ⟨c, rfl⟩)
    exact ((mem_centralizer_iff.mp (hcentral hb)) (k c) hc).symm
  let i := j.noncommCoprod k hcomm
  have hleft : (i.comp (MonoidHom.inl _ _)).range = L := by
    simpa only [i, MonoidHom.noncommCoprod_comp_inl] using hj
  have hright : (i.comp (MonoidHom.inr _ _)).range = Lx := by
    simpa only [i, MonoidHom.noncommCoprod_comp_inr] using hk
  have hi : i.range = L ⊔ Lx := by
    dsimp only [i]
    rw [MonoidHom.noncommCoprod_range, hj, hk]
  have hex := five_commutator_rank ρ i
  rw [hleft, hright] at hex
  apply hex f X x hx
    (fun g hg => by simpa only [pow_two] using
      (show g ^ 2 = 1 from elemPow_eq_one_of_isElementaryAbelian g hg))
    (fun g hg b hb => show Commute g b from
      congrArg Subtype.val (mul_comm (⟨g, hg⟩ : X) ⟨b, hb⟩))
    ?_ hsplit ?_ (by simpa only [hi] using hgen) a ha
  · intro b
    simp [i, k, MulAut.conj_apply]
  · intro b w
    simpa [i, j, k] using hf (e.symm b) w


/-- G.11.2(8) is incompatible with the original nonzero low-rank witness:
commutation with the exchanged-summand involution doubles every inner rank. -/
theorem case_eight_not_lowRank [Finite H] [IsElementaryAbelian 2 X]
    (v : V) (hv : v ≠ 0) (hc : ChapterG.Section11.CaseEight ρ B X) :
    ¬ ChapterG.Section11.LowRankWitness ρ v X := by
  intro hw
  obtain ⟨a,ha,_,hpos,hsmall,_⟩ := hw.exists_involution hv
  rcases case_eight_rank a ha hc with h | h <;> omega

/-- In G.11.2(12), only the diagonal block actions belong to the elementary
actor. Their ranks are zero or four, as are the exchanged block ranks. -/
theorem case_twelve_not_lowRank [Finite H] [IsElementaryAbelian 2 X]
    (v : V) (hv : v ≠ 0) (hc : ChapterG.Section11.CaseTwelve ρ X) :
    ¬ ChapterG.Section11.LowRankWitness ρ v X := by
  intro hw
  obtain ⟨a,ha,_,hpos,hsmall,_⟩ := hw.exists_involution hv
  rcases case_twelve_rank a ha hc with h | h <;> omega

end CatalogueExchanged
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
