module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar24

/-!
# Exact product checks on rows 1536 through 1599

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block24

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t1536 tb1536 ts1536 _ _ ts1536_sum ts1536_parity
  apply product_cons_b t1537 tb1537 ts1537 _ _ ts1537_sum ts1537_parity
  apply product_cons_b t1538 tb1538 ts1538 _ _ ts1538_sum ts1538_parity
  apply product_cons_b t1539 tb1539 ts1539 _ _ ts1539_sum ts1539_parity
  apply product_cons_b t1540 tb1540 ts1540 _ _ ts1540_sum ts1540_parity
  apply product_cons_b t1541 tb1541 ts1541 _ _ ts1541_sum ts1541_parity
  apply product_cons_b t1542 tb1542 ts1542 _ _ ts1542_sum ts1542_parity
  apply product_cons_b t1543 tb1543 ts1543 _ _ ts1543_sum ts1543_parity
  apply product_cons_b t1544 tb1544 ts1544 _ _ ts1544_sum ts1544_parity
  apply product_cons_b t1545 tb1545 ts1545 _ _ ts1545_sum ts1545_parity
  apply product_cons_b t1546 tb1546 ts1546 _ _ ts1546_sum ts1546_parity
  apply product_cons_b t1547 tb1547 ts1547 _ _ ts1547_sum ts1547_parity
  apply product_cons_b t1548 tb1548 ts1548 _ _ ts1548_sum ts1548_parity
  apply product_cons_b t1549 tb1549 ts1549 _ _ ts1549_sum ts1549_parity
  apply product_cons_b t1550 tb1550 ts1550 _ _ ts1550_sum ts1550_parity
  apply product_cons_b t1551 tb1551 ts1551 _ _ ts1551_sum ts1551_parity
  apply product_cons_b t1552 tb1552 ts1552 _ _ ts1552_sum ts1552_parity
  apply product_cons_b t1553 tb1553 ts1553 _ _ ts1553_sum ts1553_parity
  apply product_cons_b t1554 tb1554 ts1554 _ _ ts1554_sum ts1554_parity
  apply product_cons_b t1555 tb1555 ts1555 _ _ ts1555_sum ts1555_parity
  apply product_cons_b t1556 tb1556 ts1556 _ _ ts1556_sum ts1556_parity
  apply product_cons_b t1557 tb1557 ts1557 _ _ ts1557_sum ts1557_parity
  apply product_cons_b t1558 tb1558 ts1558 _ _ ts1558_sum ts1558_parity
  apply product_cons_b t1559 tb1559 ts1559 _ _ ts1559_sum ts1559_parity
  apply product_cons_b t1560 tb1560 ts1560 _ _ ts1560_sum ts1560_parity
  apply product_cons_b t1561 tb1561 ts1561 _ _ ts1561_sum ts1561_parity
  apply product_cons_b t1562 tb1562 ts1562 _ _ ts1562_sum ts1562_parity
  apply product_cons_b t1563 tb1563 ts1563 _ _ ts1563_sum ts1563_parity
  apply product_cons_b t1564 tb1564 ts1564 _ _ ts1564_sum ts1564_parity
  apply product_cons_b t1565 tb1565 ts1565 _ _ ts1565_sum ts1565_parity
  apply product_cons_b t1566 tb1566 ts1566 _ _ ts1566_sum ts1566_parity
  apply product_cons_b t1567 tb1567 ts1567 _ _ ts1567_sum ts1567_parity
  apply product_cons_b t1568 tb1568 ts1568 _ _ ts1568_sum ts1568_parity
  apply product_cons_b t1569 tb1569 ts1569 _ _ ts1569_sum ts1569_parity
  apply product_cons_b t1570 tb1570 ts1570 _ _ ts1570_sum ts1570_parity
  apply product_cons_b t1571 tb1571 ts1571 _ _ ts1571_sum ts1571_parity
  apply product_cons_b t1572 tb1572 ts1572 _ _ ts1572_sum ts1572_parity
  apply product_cons_b t1573 tb1573 ts1573 _ _ ts1573_sum ts1573_parity
  apply product_cons_b t1574 tb1574 ts1574 _ _ ts1574_sum ts1574_parity
  apply product_cons_b t1575 tb1575 ts1575 _ _ ts1575_sum ts1575_parity
  apply product_cons_b t1576 tb1576 ts1576 _ _ ts1576_sum ts1576_parity
  apply product_cons_b t1577 tb1577 ts1577 _ _ ts1577_sum ts1577_parity
  apply product_cons_b t1578 tb1578 ts1578 _ _ ts1578_sum ts1578_parity
  apply product_cons_b t1579 tb1579 ts1579 _ _ ts1579_sum ts1579_parity
  apply product_cons_b t1580 tb1580 ts1580 _ _ ts1580_sum ts1580_parity
  apply product_cons_b t1581 tb1581 ts1581 _ _ ts1581_sum ts1581_parity
  apply product_cons_b t1582 tb1582 ts1582 _ _ ts1582_sum ts1582_parity
  apply product_cons_b t1583 tb1583 ts1583 _ _ ts1583_sum ts1583_parity
  apply product_cons_b t1584 tb1584 ts1584 _ _ ts1584_sum ts1584_parity
  apply product_cons_b t1585 tb1585 ts1585 _ _ ts1585_sum ts1585_parity
  apply product_cons_b t1586 tb1586 ts1586 _ _ ts1586_sum ts1586_parity
  apply product_cons_b t1587 tb1587 ts1587 _ _ ts1587_sum ts1587_parity
  apply product_cons_b t1588 tb1588 ts1588 _ _ ts1588_sum ts1588_parity
  apply product_cons_b t1589 tb1589 ts1589 _ _ ts1589_sum ts1589_parity
  apply product_cons_b t1590 tb1590 ts1590 _ _ ts1590_sum ts1590_parity
  apply product_cons_b t1591 tb1591 ts1591 _ _ ts1591_sum ts1591_parity
  apply product_cons_b t1592 tb1592 ts1592 _ _ ts1592_sum ts1592_parity
  apply product_cons_b t1593 tb1593 ts1593 _ _ ts1593_sum ts1593_parity
  apply product_cons_b t1594 tb1594 ts1594 _ _ ts1594_sum ts1594_parity
  apply product_cons_b t1595 tb1595 ts1595 _ _ ts1595_sum ts1595_parity
  apply product_cons_b t1596 tb1596 ts1596 _ _ ts1596_sum ts1596_parity
  apply product_cons_b t1597 tb1597 ts1597 _ _ ts1597_sum ts1597_parity
  apply product_cons_b t1598 tb1598 ts1598 _ _ ts1598_sum ts1598_parity
  apply product_cons_b t1599 tb1599 ts1599 _ _ ts1599_sum ts1599_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d1536 da1536 ds1536 _ _ ds1536_sum ds1536_parity
  apply product_cons_a d1537 da1537 ds1537 _ _ ds1537_sum ds1537_parity
  apply product_cons_a d1538 da1538 ds1538 _ _ ds1538_sum ds1538_parity
  apply product_cons_a d1539 da1539 ds1539 _ _ ds1539_sum ds1539_parity
  apply product_cons_a d1540 da1540 ds1540 _ _ ds1540_sum ds1540_parity
  apply product_cons_a d1541 da1541 ds1541 _ _ ds1541_sum ds1541_parity
  apply product_cons_a d1542 da1542 ds1542 _ _ ds1542_sum ds1542_parity
  apply product_cons_a d1543 da1543 ds1543 _ _ ds1543_sum ds1543_parity
  apply product_cons_a d1544 da1544 ds1544 _ _ ds1544_sum ds1544_parity
  apply product_cons_a d1545 da1545 ds1545 _ _ ds1545_sum ds1545_parity
  apply product_cons_a d1546 da1546 ds1546 _ _ ds1546_sum ds1546_parity
  apply product_cons_a d1547 da1547 ds1547 _ _ ds1547_sum ds1547_parity
  apply product_cons_a d1548 da1548 ds1548 _ _ ds1548_sum ds1548_parity
  apply product_cons_a d1549 da1549 ds1549 _ _ ds1549_sum ds1549_parity
  apply product_cons_a d1550 da1550 ds1550 _ _ ds1550_sum ds1550_parity
  apply product_cons_a d1551 da1551 ds1551 _ _ ds1551_sum ds1551_parity
  apply product_cons_a d1552 da1552 ds1552 _ _ ds1552_sum ds1552_parity
  apply product_cons_a d1553 da1553 ds1553 _ _ ds1553_sum ds1553_parity
  apply product_cons_a d1554 da1554 ds1554 _ _ ds1554_sum ds1554_parity
  apply product_cons_a d1555 da1555 ds1555 _ _ ds1555_sum ds1555_parity
  apply product_cons_a d1556 da1556 ds1556 _ _ ds1556_sum ds1556_parity
  apply product_cons_a d1557 da1557 ds1557 _ _ ds1557_sum ds1557_parity
  apply product_cons_a d1558 da1558 ds1558 _ _ ds1558_sum ds1558_parity
  apply product_cons_a d1559 da1559 ds1559 _ _ ds1559_sum ds1559_parity
  apply product_cons_a d1560 da1560 ds1560 _ _ ds1560_sum ds1560_parity
  apply product_cons_a d1561 da1561 ds1561 _ _ ds1561_sum ds1561_parity
  apply product_cons_a d1562 da1562 ds1562 _ _ ds1562_sum ds1562_parity
  apply product_cons_a d1563 da1563 ds1563 _ _ ds1563_sum ds1563_parity
  apply product_cons_a d1564 da1564 ds1564 _ _ ds1564_sum ds1564_parity
  apply product_cons_a d1565 da1565 ds1565 _ _ ds1565_sum ds1565_parity
  apply product_cons_a d1566 da1566 ds1566 _ _ ds1566_sum ds1566_parity
  apply product_cons_a d1567 da1567 ds1567 _ _ ds1567_sum ds1567_parity
  apply product_cons_a d1568 da1568 ds1568 _ _ ds1568_sum ds1568_parity
  apply product_cons_a d1569 da1569 ds1569 _ _ ds1569_sum ds1569_parity
  apply product_cons_a d1570 da1570 ds1570 _ _ ds1570_sum ds1570_parity
  apply product_cons_a d1571 da1571 ds1571 _ _ ds1571_sum ds1571_parity
  apply product_cons_a d1572 da1572 ds1572 _ _ ds1572_sum ds1572_parity
  apply product_cons_a d1573 da1573 ds1573 _ _ ds1573_sum ds1573_parity
  apply product_cons_a d1574 da1574 ds1574 _ _ ds1574_sum ds1574_parity
  apply product_cons_a d1575 da1575 ds1575 _ _ ds1575_sum ds1575_parity
  apply product_cons_a d1576 da1576 ds1576 _ _ ds1576_sum ds1576_parity
  apply product_cons_a d1577 da1577 ds1577 _ _ ds1577_sum ds1577_parity
  apply product_cons_a d1578 da1578 ds1578 _ _ ds1578_sum ds1578_parity
  apply product_cons_a d1579 da1579 ds1579 _ _ ds1579_sum ds1579_parity
  apply product_cons_a d1580 da1580 ds1580 _ _ ds1580_sum ds1580_parity
  apply product_cons_a d1581 da1581 ds1581 _ _ ds1581_sum ds1581_parity
  apply product_cons_a d1582 da1582 ds1582 _ _ ds1582_sum ds1582_parity
  apply product_cons_a d1583 da1583 ds1583 _ _ ds1583_sum ds1583_parity
  apply product_cons_a d1584 da1584 ds1584 _ _ ds1584_sum ds1584_parity
  apply product_cons_a d1585 da1585 ds1585 _ _ ds1585_sum ds1585_parity
  apply product_cons_a d1586 da1586 ds1586 _ _ ds1586_sum ds1586_parity
  apply product_cons_a d1587 da1587 ds1587 _ _ ds1587_sum ds1587_parity
  apply product_cons_a d1588 da1588 ds1588 _ _ ds1588_sum ds1588_parity
  apply product_cons_a d1589 da1589 ds1589 _ _ ds1589_sum ds1589_parity
  apply product_cons_a d1590 da1590 ds1590 _ _ ds1590_sum ds1590_parity
  apply product_cons_a d1591 da1591 ds1591 _ _ ds1591_sum ds1591_parity
  apply product_cons_a d1592 da1592 ds1592 _ _ ds1592_sum ds1592_parity
  apply product_cons_a d1593 da1593 ds1593 _ _ ds1593_sum ds1593_parity
  apply product_cons_a d1594 da1594 ds1594 _ _ ds1594_sum ds1594_parity
  apply product_cons_a d1595 da1595 ds1595 _ _ ds1595_sum ds1595_parity
  apply product_cons_a d1596 da1596 ds1596 _ _ ds1596_sum ds1596_parity
  apply product_cons_a d1597 da1597 ds1597 _ _ ds1597_sum ds1597_parity
  apply product_cons_a d1598 da1598 ds1598 _ _ ds1598_sum ds1598_parity
  apply product_cons_a d1599 da1599 ds1599 _ _ ds1599_sum ds1599_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 1536).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 1536).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 1536).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 1536).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 1536).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 1536).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 1536).take 64) RightCertificate.wideSecond ((tbRows.drop 1536).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 1536).take 64) RightCertificate.wideFirst ((daRows.drop 1536).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block24
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
