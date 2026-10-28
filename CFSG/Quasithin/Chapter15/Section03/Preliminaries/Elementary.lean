module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupTheory.PGroup.IndexTwoOmegaCenter
public import Theory.GroupTheory.PGroup.OmegaImage

/-!
# Elementary steps in the local preliminaries of Section 15.3

The central omega argument is transported from the group `T` to the common
ambient group. Its explicit inputs are the index-two plane stabilizer, the
central involution of `T`, and the four-element fixed plane supplied by the
natural orthogonal action.

The order-three-generated subgroup is invariant under normalizers. If it
recovers `Y` from `Y ker(f)`, this gives the normalizer of the image of `Y`
under a surjective homomorphism. This is the lifting step in 15.3.11(9);
it does not assume that normalizers always commute with quotients.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas 15.3.8
and 15.3.11, printed pp.1122–1124. The geometric and local-structure inputs
remain explicit here and must be discharged in the section assembly.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03

open Subgroup

variable {G : Type*} [Group G]

/-- The central omega subgroup of an arbitrary subgroup, in the ambient group. -/
def centralOmegaIn (S : Subgroup G) : Subgroup G :=
  (omegaOneAmbient (center S)).map S.subtype

/-- The central omega subgroup of a Sylow group uses the existing source convention. -/
theorem centralOmegaIn_sylow (T : Sylow 2 G) :
    centralOmegaIn (T : Subgroup G) = centralInvolutions T := rfl

/-- The ambient form of 15.3.8, with exactly the geometric facts used by its proof. -/
theorem fixedPlane_eq_centralOmegaIn [Finite G]
    (T : Sylow 2 G) (V S : Subgroup G)
    (hST : S ≤ (T : Subgroup G))
    (hindex : (S.subgroupOf (T : Subgroup G)).index = 2)
    (hZ : Nat.card (centralInvolutions T) = 2)
    [IsElementaryAbelian 2 (fixedPlane V S)]
    (hfixed : fixedPlane V S ≤ S) (hcard : Nat.card (fixedPlane V S) = 4) :
    fixedPlane V S = centralOmegaIn S := by
  let S₀ := S.subgroupOf (T : Subgroup G)
  have hZ₀ : Nat.card (omega₁ (center T) (p := 2)) = 2 := by
    simpa only [centralInvolutions, ChapterA.Section05To06.centralOmega,
      card_map_of_injective (T : Subgroup G).subtype_injective,
      card_map_of_injective (center T).subtype_injective] using hZ
  have hbound := card_omega_center_le_sq_of_index_two S₀ hindex
  rw [hZ₀] at hbound
  have hcardS : Nat.card (omega₁ (center S) (p := 2)) ≤ 4 := by
    let e := subgroupOfEquivOfLe hST
    let ec : center S₀ ≃* center S := centerCongr e
    have homega : (omega₁ (center S₀) (p := 2)).map ec.toMonoidHom =
        omega₁ (center S) (p := 2) := by
      exact ec.map_omega 2 1
    rw [← homega, card_map_of_injective ec.injective]
    exact hbound
  have hle : fixedPlane V S ≤ centralOmegaIn S := by
    intro x hx
    let z : center S := ⟨⟨x, hfixed hx⟩, mem_center_iff.mpr (by
      intro s
      exact Subtype.ext (hx.2 s s.property))⟩
    refine mem_map.mpr ⟨(z : S), ?_, rfl⟩
    refine mem_map.mpr ⟨z, subset_closure ?_, rfl⟩
    change z ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    change x ^ 2 = 1
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  apply eq_of_le_of_card_ge hle
  simpa only [centralOmegaIn, omegaOneAmbient,
    card_map_of_injective S.subtype_injective,
    card_map_of_injective (center S).subtype_injective, hcard] using hcardS

/-- The order-three-generated subgroup lies in its original subgroup. -/
theorem theta_le (X : Subgroup G) : theta X ≤ X :=
  (closure_le _).mpr fun _ hx => hx.1

/-- Monotonicity is used between `Y₊`, `Y₊ C_I(U_I)`, and `M_I`. -/
theorem theta_mono {X Y : Subgroup G} (h : X ≤ Y) : theta X ≤ theta Y :=
  closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

/-- Taking the order-three-generated subgroup twice does not change it. -/
theorem theta_idempotent (X : Subgroup G) : theta (theta X) = theta X := by
  apply le_antisymm (theta_le _) ((closure_le _).mpr ?_)
  intro x hx
  exact subset_closure ⟨subset_closure hx, hx.2⟩

/-- The source's `θ(X)` is preserved by every ambient normalizer of `X`. -/
theorem normalizer_le_normalizer_theta (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (theta X : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hmap : (theta X).map (MulAut.conj g).toMonoidHom ≤ theta X := by
    rw [theta, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact subset_closure ⟨(hg y).mp hy.1, ((MulAut.conj g).orderOf_eq y).trans hy.2⟩
  exact hmap (mem_map_of_mem _ hx)

/-- Recovering `Y` by `θ` prevents extra normalizers from appearing in a quotient. -/
theorem normalizer_image_eq_of_theta_preimage
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (Y : Subgroup G) (hY : theta (Y ⊔ f.ker) = Y) :
    normalizer (Y.map f : Set H) = (normalizer (Y : Set G)).map f := by
  apply le_antisymm ?_ (Y.le_normalizer_map f)
  intro x hx
  obtain ⟨g, rfl⟩ := hf x
  have hg : g ∈ (normalizer (Y.map f : Set H)).comap f := hx
  rw [comap_normalizer_eq_of_surjective _ hf, comap_map_eq] at hg
  have hN := normalizer_le_normalizer_theta (Y ⊔ f.ker) hg
  rw [hY] at hN
  exact mem_map_of_mem f hN

/-- The monotone sandwich in the proof of 15.3.11(9). -/
theorem theta_sup_kernel_eq {Y M K : Subgroup G}
    (hYM : Y ≤ M) (hKM : K ≤ M) (hθ : theta M = Y) :
    theta (Y ⊔ K) = Y := by
  apply le_antisymm
  · exact (theta_mono (sup_le hYM hKM)).trans_eq hθ
  · have hfix : theta Y = Y := by rw [← hθ, theta_idempotent]
    calc
      Y = theta Y := hfix.symm
      _ ≤ theta (Y ⊔ K) := theta_mono le_sup_left

/-- The quotient-normalizer equality in 15.3.11(9), from (2), (4), and (6).
Here `f` can be the actual map `I → I/C_I(U_I)`. -/
theorem image_normalizer_of_theta
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (Y M : Subgroup G) (hYM : Y ≤ M) (hker : f.ker ≤ M)
    (hθ : theta M = Y) (hN : normalizer (Y : Set G) = M) :
    normalizer (Y.map f : Set H) = M.map f := by
  rw [normalizer_image_eq_of_theta_preimage f hf Y
    (theta_sup_kernel_eq hYM hker hθ), hN]

/-- A subgroup containing the kernel remains proper after a surjection. -/
theorem image_lt_top_of_kernel_le
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup G) (hker : f.ker ≤ M) (hM : M < ⊤) : M.map f < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  apply hM.ne
  apply map_injective_of_ker_le f hker le_top
  rw [h, map_top_of_surjective f hf]

/-- Nontrivial action on `U` ensures a nontrivial image modulo its centralizer. -/
theorem image_ne_bot_of_not_centralizing
    {H : Type*} [Group H] (f : G →* H) (Y U : Subgroup G)
    (hker : f.ker ≤ centralizer (U : Set G))
    (hact : ¬ Y ≤ centralizer (U : Set G)) : Y.map f ≠ ⊥ := by
  intro h
  exact hact (((map_eq_bot_iff Y).mp h).trans hker)

/-- Transport `θ` through a faithful embedding, in particular a subgroup subtype. -/
theorem theta_map_of_injective
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f)
    (X : Subgroup G) : (theta X).map f = theta (X.map f) := by
  rw [theta, theta, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨mem_map_of_mem f hy.1, (orderOf_injective f hf y).trans hy.2⟩
  · rintro ⟨⟨y, hy, rfl⟩, ho⟩
    exact ⟨y, ⟨hy, (orderOf_injective f hf y).symm.trans ho⟩, rfl⟩

/-- The centralizer containment in 15.3.11(2), uniformly for the two choices
of `Y₊`. In the first choice take `W = V`; in the second take `W = V₂`. -/
theorem centralizer_localSpan_le_intersection
    (Z Yplus I M W : Subgroup G) (hYI : Yplus ≤ I)
    (hspan : W ≤ localSpan Z Yplus) (hcontrol : normalizer (W : Set G) ≤ M) :
    I ⊓ centralizer (localSpan Z I : Set G) ≤ M ⊓ I := by
  have hWI : W ≤ localSpan Z I := hspan.trans (conjugateSpanBy_mono le_rfl hYI)
  exact fun _ hx =>
    ⟨hcontrol (Subgroup.centralizer_le_normalizer _ (centralizer_le hWI hx.2)), hx.1⟩

/-- Once (6) has identified `Y₊`, the normalizer control in (3) gives (4).
The normalization by `M ∩ I` is derived from the order-three generators. -/
theorem normalizer_in_eq_of_theta
    (Yplus M I : Subgroup G) (hθ : theta (M ⊓ I) = Yplus)
    (hcontrol : normalizer (Yplus : Set G) ≤ M) :
    I ⊓ normalizer (Yplus : Set G) = M ⊓ I := by
  apply le_antisymm (fun _ hx => ⟨hcontrol hx.2, hx.1⟩)
  intro x hx
  refine ⟨hx.2, ?_⟩
  rw [← hθ]
  exact normalizer_le_normalizer_theta _ ((M ⊓ I).le_normalizer hx)

/-- The characteristic-subgroup argument in 15.3.11(12).
The uniqueness premise is supplied by 15.3.2(4) for
`D = O²(Y ∩ L)`. All normality is in the indicated overgroup. -/
theorem no_characteristic_subgroup_normal_in_join [Finite G]
    (T : Sylow 2 G) (S L D M : Subgroup G)
    (hST : S ≤ (T : Subgroup G))
    (hSn : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hDL : D ≤ L) (hL : ¬ L ≤ M)
    (hunique : Chapter4.UniqueMaximalOvergroup (D ⊔ (T : Subgroup G)) M)
    (C : Subgroup S) [C.Characteristic] (hC : C ≠ ⊥) :
    ¬ ((C.map S.subtype).subgroupOf (L ⊔ S)).Normal := by
  intro hn
  let A := C.map S.subtype
  have hAle : A ≤ S := map_subtype_le _
  have hAne : A ≠ ⊥ := fun h =>
    hC ((C.map_eq_bot_iff_of_injective S.subtype_injective).mp h)
  have hAtwo : IsPGroup 2 A := T.isPGroup'.to_le (hAle.trans hST)
  have hLA : L ≤ normalizer (A : Set G) :=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
      (hAle.trans le_sup_right)).mp hn)
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    hSn.trans (normalizer_le_normalizer_characteristic_image S C)
  have hlocal : IsTwoLocal (normalizer (A : Set G)) := ⟨A, hAne, hAtwo, rfl⟩
  obtain ⟨N, hAN, hN⟩ := Finite.exists_le_maximal hlocal
  have hDN : D ⊔ (T : Subgroup G) ≤ N := sup_le (hDL.trans (hLA.trans hAN)) (hTA.trans hAN)
  have hNM := hunique.2.2 N hN hDN
  exact hL (hNM ▸ hLA.trans hAN)

end CFSG.Quasithin.Chapter15.Section03

end
