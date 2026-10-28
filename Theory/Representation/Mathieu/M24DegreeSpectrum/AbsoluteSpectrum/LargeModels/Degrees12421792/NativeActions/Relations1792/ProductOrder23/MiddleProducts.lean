module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.MiddleProducts.Checks

/-!
# The two middle products in the degree-1792 addition chain

The complete literal checks establish C3*C2 = C5 and C5*C5 = C10.
The names Ck still denote the fixed candidate matrices: no earlier power
certificate is a premise. All 1792 rows of each product are checked, using
sixteen-row right blocks and thirty-two-row certificate blocks. Explicit
coefficient digits are checked to reconstruct each original row.

These are exactly premises `h5` and `h10` of
`Relations1792.product_order23_of_checks`. Final assembly of (A*B)^23 = 1
also needs the independently owned low and high products.

Source: untransposed ATLAS M24G1-f2r1792B0 matrices and M24G1-P1 word 2.
See `MiddleProducts/source/README.md` for provenance and reproduction.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.MiddleProducts

open ProductOrder23.Data ProductOrder23.Certificate

/-- Every row of the literal fifth-power candidate product. -/
theorem fifth : check power3Rows power2Rows power5Rows = true := by
  have hc : Blocked.checkBlocks Tables.third Tables.second Tables.fifth = true := by
    simp only [Tables.third, Tables.fifth, Blocked.checkBlocks,
      Checks.fifth00, Checks.fifth01, Checks.fifth02, Checks.fifth03, Checks.fifth04, Checks.fifth05, Checks.fifth06,
      Checks.fifth07, Checks.fifth08, Checks.fifth09, Checks.fifth10, Checks.fifth11, Checks.fifth12, Checks.fifth13,
      Checks.fifth14, Checks.fifth15, Checks.fifth16, Checks.fifth17, Checks.fifth18, Checks.fifth19, Checks.fifth20,
      Checks.fifth21, Checks.fifth22, Checks.fifth23, Checks.fifth24, Checks.fifth25, Checks.fifth26, Checks.fifth27,
      Checks.fifth28, Checks.fifth29, Checks.fifth30, Checks.fifth31, Checks.fifth32, Checks.fifth33, Checks.fifth34,
      Checks.fifth35, Checks.fifth36, Checks.fifth37, Checks.fifth38, Checks.fifth39, Checks.fifth40, Checks.fifth41,
      Checks.fifth42, Checks.fifth43, Checks.fifth44, Checks.fifth45, Checks.fifth46, Checks.fifth47, Checks.fifth48,
      Checks.fifth49, Checks.fifth50, Checks.fifth51, Checks.fifth52, Checks.fifth53, Checks.fifth54, Checks.fifth55, Bool.true_and]
  have h := Blocked.checkBlocks_sound _ _ _ Tables.second_lengths hc
  rw [Tables.third_eq, Tables.second_eq, Tables.fifth_eq] at h
  exact h

/-- Every row of the literal tenth-power candidate product. -/
theorem tenth : check power5Rows power5Rows power10Rows = true := by
  have hc : Blocked.checkBlocks Tables.fifth Tables.fifthRight Tables.tenth = true := by
    simp only [Tables.fifth, Tables.tenth, Blocked.checkBlocks,
      Checks.tenth00, Checks.tenth01, Checks.tenth02, Checks.tenth03, Checks.tenth04, Checks.tenth05, Checks.tenth06,
      Checks.tenth07, Checks.tenth08, Checks.tenth09, Checks.tenth10, Checks.tenth11, Checks.tenth12, Checks.tenth13,
      Checks.tenth14, Checks.tenth15, Checks.tenth16, Checks.tenth17, Checks.tenth18, Checks.tenth19, Checks.tenth20,
      Checks.tenth21, Checks.tenth22, Checks.tenth23, Checks.tenth24, Checks.tenth25, Checks.tenth26, Checks.tenth27,
      Checks.tenth28, Checks.tenth29, Checks.tenth30, Checks.tenth31, Checks.tenth32, Checks.tenth33, Checks.tenth34,
      Checks.tenth35, Checks.tenth36, Checks.tenth37, Checks.tenth38, Checks.tenth39, Checks.tenth40, Checks.tenth41,
      Checks.tenth42, Checks.tenth43, Checks.tenth44, Checks.tenth45, Checks.tenth46, Checks.tenth47, Checks.tenth48,
      Checks.tenth49, Checks.tenth50, Checks.tenth51, Checks.tenth52, Checks.tenth53, Checks.tenth54, Checks.tenth55, Bool.true_and]
  have h := Blocked.checkBlocks_sound _ _ _ Tables.fifthRight_lengths hc
  rw [Tables.fifth_eq, Tables.fifthRight_eq, Tables.tenth_eq] at h
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.MiddleProducts
